-- Prove2me | Definitions.Def_OAIE3v2B033
-- name    : OAIE3v2B033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:34.706369+00:00
-- url     : https://prove2.me/theorems/bcb304ef-ad61-4898-b988-d75ba30a3247
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 34 of 311
-- statement:
--   Definitions bundle 34 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CanonicalZeroLayerBudgetedInitialization.lean`, `Dynamics/EarlyFiberCapBudget.lean`, `Dynamics/JointExceptionalGainBudget.lean`, `Dynamics/ModeAmplitudeErrorBudget.lean`, `Dynamics/NativeLocalPivotVerticalBudget.lean`, `Dynamics/PatchTopNetBudget.lean`, `Dynamics/PhysicalBadProductErrorBudget.lean`, `Dynamics/PreparedFiniteForwardFrontProfileBudget.lean`, `Estimates/AllocatedMaskedFactorBounds.lean`, `Estimates/CanonicalScalarSourceEnvelope.lean`, `Estimates/ComplexNormalizationError.lean`, `Estimates/DiscreteMinorThreshold.lean`, `Estimates/LocalAverageAmplitude.lean`, `Estimates/NativeLocalPivotVerticalPartners.lean`, `Estimates/NormalizedDeterminantCutoff.lean`, `Estimates/NormalizedFixedPatchFunction.lean`, `Estimates/PreparedEnlargedModularAllocation.lean`, `Estimates/PreparedFiniteScheduleLocalScalarConstruction.lean`, `Estimates/PrincipalCoefficientSource.lean`, `Estimates/ScalarBadSublevelRamp.lean`, `Estimates/UnitBoundProductDifference.lean`, `Estimates/UnitTestClipping.lean`, `Geometry/CoordinateDeterminant.lean`, `Geometry/NormalizedSpatialChoiceBudget.lean`, `Lattices/AllocatedCenteredBadPrimeSurrogate.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/IntegerPMFNormalizedSource.lean`, `Lattices/LargestBadPrimeProduct.lean`, `Lattices/ModularCoefficientBadPrimeProduct.lean`, `Lattices/StrideSelectedResidueBadProduct.lean`, `Linear/AllocatedKernelPrimitiveBudget.lean`, `Linear/AllocatedModularRankCongruenceOutput.lean`, `Linear/AllocatedModularRankPreparedBlocks.lean`, `Linear/CoordinateZeroProjection.lean`, `Linear/JointKernelCutoffBudget.lean`, `Linear/PreparedFiniteNestedSourceProjectionBudget.lean`, `Linear/PreparedSpatialKernelBlocks.lean`, `Linear/SmoothMatrixBlockBudget.lean`, `Linear/SpatialMatrixBlockWideProbability.lean`, `Polynomial/EmbeddedMatrixDeterminantPolynomial.lean`, `Polynomial/PolynomialAnalyticDerivative.lean`, `Polynomial/PolynomialDeterminantDegree.lean`, `Polynomial/PolynomialDeterminantDerivativeBound.lean`, `Polynomial/PolynomialSublevelThresholdBudget.lean`, `Polynomial/ShiftedSmoothPolynomialSublevel.lean`, `Polynomial/UnivariatePolynomialSublevel.lean`, `Probability/DensityIntegralBound.lean`, `Probability/FiniteExcessMassCap.lean`, `Probability/PivotDensitySupport.lean`, `Probability/PreparedGeometryConditionalExcess.lean`, `Sampling/ForecastPreparedScaleBudget.lean`, `Sampling/ForecastRawSpatialBoxReorder.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalAverageAmplitude
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem norm_local_average_amplitude_le {G X : Type*} [Fintype X] [Nonempty X]
    (point : X → G) (f amplitude : G → ℂ) (base : G)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hamp : ‖amplitude base‖ ≤ 1)
    {η β : ℝ} (hvariation : ∀ u, ‖amplitude (point u) - amplitude base‖ ≤ η)
    (hlocal : ‖𝔼 u, f (point u)‖ ≤ β) :
    ‖𝔼 u, amplitude (point u) * f (point u)‖ ≤ η + β := by
  have he : (𝔼 u, amplitude (point u) * f (point u)) =
      (𝔼 u, (amplitude (point u) - amplitude base) * f (point u)) +
        amplitude base * (𝔼 u, f (point u)) := by
    rw [Finset.mul_expect, ← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro u _
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect (fun u _ => ?_)).trans_eq (Fintype.expect_const η)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)).trans (by simpa using hvariation u)
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hamp (norm_nonneg _)).trans (by simpa using hlocal)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialAnalyticDerivative
namespace OAI

section

namespace Erdos3

open scoped ContDiff

theorem mvPolynomial_contDiff_eval {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) : ContDiff ℝ ∞ (fun a : ι → ℝ => MvPolynomial.eval a p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa only [MvPolynomial.eval_C] using (contDiff_const (c := r))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    have h := hp.mul (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff
    simp only [ContinuousLinearMap.proj_apply] at h
    simp only [map_mul, MvPolynomial.eval_X]
    exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_prod_eval_abs_le {I K : Type*} (s : Finset K)
    (p : K → MvPolynomial I ℝ) (a : I → ℝ) {L : ℝ}
    (hp : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L) :
    |MvPolynomial.eval a (∏ k ∈ s, p k)| ≤ L ^ s.card := by
  rw [map_prod, Finset.abs_prod]
  calc
    _ ≤ ∏ _k ∈ s, L := Finset.prod_le_prod (fun _ _ => abs_nonneg _) hp
    _ = _ := by simp

theorem mvPolynomial_prod_pderiv_eval_abs_le_of_bound {I K : Type*} (s : Finset K)
    (p : K → MvPolynomial I ℝ) (j : I) (a : I → ℝ) {L D : ℝ}
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hp : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L)
    (hd : ∀ k ∈ s, |MvPolynomial.eval a (MvPolynomial.pderiv j (p k))| ≤ D) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (∏ k ∈ s, p k))| ≤
      s.card * D * L ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hL0 : 0 ≤ L := zero_le_one.trans hL
    have hps : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L :=
      fun k hk => hp k (Finset.mem_insert_of_mem hk)
    have hds : ∀ k ∈ s, |MvPolynomial.eval a (MvPolynomial.pderiv j (p k))| ≤ D :=
      fun k hk => hd k (Finset.mem_insert_of_mem hk)
    have hprod := mvPolynomial_prod_eval_abs_le s p a hps
    have hder := ih hps hds
    rw [Finset.prod_insert hi, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
    calc
      _ ≤ |MvPolynomial.eval a (MvPolynomial.pderiv j (p i))| *
          |MvPolynomial.eval a (∏ k ∈ s, p k)| +
          |MvPolynomial.eval a (p i)| * |MvPolynomial.eval a (MvPolynomial.pderiv j (∏ k ∈ s, p k))| :=
        (abs_add_le _ _).trans_eq (by simp only [abs_mul])
      _ ≤ D * L ^ s.card + L * (s.card * D * L ^ s.card) :=
        add_le_add (mul_le_mul (hd i (Finset.mem_insert_self i s)) hprod (abs_nonneg _) hD)
          (mul_le_mul (hp i (Finset.mem_insert_self i s)) hder (abs_nonneg _) hL0)
      _ ≤ L * (D * L ^ s.card) + L * (s.card * D * L ^ s.card) := by
        apply add_le_add _ le_rfl
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hL (mul_nonneg hD (pow_nonneg hL0 _))
      _ = _ := by rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, pow_succ]; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_det_eval_function {I O : Type*} [Fintype O] [DecidableEq O]
    (M : Matrix O O (MvPolynomial I ℝ)) :
    (fun a => (M.map (MvPolynomial.eval a)).det) = (fun a => MvPolynomial.eval a M.det) := by
  funext a
  have h := (MvPolynomial.eval a).map_det M
  simp only [RingHom.mapMatrix_apply] at h
  exact h.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UnivariatePolynomialSublevel
namespace OAI

section

namespace Erdos3

open MeasureTheory Polynomial
open scoped BigOperators

noncomputable def univariateSublevelConstant (d : ℕ) : ℝ :=
  ((d + 1 : ℝ) * (8 * (d + 1 : ℝ)) ^ d) ^ ((d : ℝ)⁻¹)

theorem univariateSublevelConstant_pos (d : ℕ) : 0 < univariateSublevelConstant d := by
  unfold univariateSublevelConstant
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_det_degreeOf_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial κ ℝ)) (j : κ) (e : ℕ)
    (hM : ∀ a b, (M a b).degreeOf j ≤ e) :
    M.det.degreeOf j ≤ Fintype.card ι * e := by
  classical
  rw [Matrix.det_apply']
  apply (MvPolynomial.degreeOf_sum_le j Finset.univ _).trans
  apply Finset.sup_le
  intro σ _
  have hsign : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial κ ℝ)) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℝ) := by simp
  rw [hsign]
  apply (MvPolynomial.degreeOf_C_mul_le _ j _).trans
  apply (MvPolynomial.degreeOf_prod_le j Finset.univ _).trans
  calc
    _ ≤ ∑ _a : ι, e := Finset.sum_le_sum (fun a _ => hM (σ a) a)
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateDeterminant
namespace OAI

section

namespace Erdos3

noncomputable def coordinateMatrixPolynomial {I X : Type*} (index : I → I → X) :
    Matrix I I (MvPolynomial X ℝ) := fun i j => MvPolynomial.X (index i j)

theorem coordinateMatrixPolynomial_eval {I X : Type*} [Fintype I] [DecidableEq I]
    (index : I → I → X) (x : X → ℝ) :
    MvPolynomial.eval x (coordinateMatrixPolynomial index).det =
      Matrix.det (fun i j => x (index i j)) := by
  rw [(MvPolynomial.eval x).map_det]
  congr 1
  ext i j
  change MvPolynomial.eval x (MvPolynomial.X (index i j) : MvPolynomial X ℝ) = x (index i j)
  simp only [MvPolynomial.eval_X]

theorem coordinateMatrixPolynomial_degree {I X : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq X] (index : I → I → X) (j : X) :
    (coordinateMatrixPolynomial index).det.degreeOf j ≤ Fintype.card I := by
  apply (polynomial_det_degreeOf_le _ j 1 ?_).trans_eq (Nat.mul_one _)
  intro a b
  simp only [coordinateMatrixPolynomial, MvPolynomial.degreeOf_X]
  split_ifs <;> omega

noncomputable def coordinateDeterminantVariation (I X : Type*) [Fintype I] [Fintype X] : ℝ :=
  Fintype.card X * ((Fintype.card I).factorial * Fintype.card I)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.EmbeddedMatrixDeterminantPolynomial
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def multivariateSublevelConstant (N d : ℕ) : ℝ :=
  (2 : ℝ) ^ N * N * univariateSublevelConstant d

theorem multivariateSublevelConstant_pos {N : ℕ} (hN : 0 < N) (d : ℕ) :
    0 < multivariateSublevelConstant N d := by
  unfold multivariateSublevelConstant
  exact mul_pos (mul_pos (by positivity) (by exact_mod_cast hN)) (univariateSublevelConstant_pos d)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Pointwise

def boxMvPolynomialSublevel {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (R u : ℝ) : Set (Fin N → ℝ) :=
  {x | (∀ i, |x i| ≤ R) ∧ |MvPolynomial.eval x p| ≤ u}

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {n N : ℕ}

noncomputable def embeddedMatrixDeterminantPolynomial
    (e : Fin n × Fin n ↪ Fin N) : MvPolynomial (Fin N) ℝ :=
  (coordinateMatrixPolynomial (fun i j => e (i,j))).det

noncomputable def embeddedMatrixIdentityPoint
    (e : Fin n × Fin n ↪ Fin N) (k : Fin N) : ℝ :=
  if ∃ i : Fin n, e (i,i) = k then 1 else 0

theorem embeddedMatrixIdentityPoint_entry (e : Fin n × Fin n ↪ Fin N) (a b : Fin n) :
    embeddedMatrixIdentityPoint e (e (a,b)) = if a = b then 1 else 0 := by
  have hdiag : (∃ i : Fin n, e (i,i) = e (a,b)) ↔ a = b := by
    constructor
    · rintro ⟨i,hi⟩
      have hh := e.injective hi
      exact (congrArg Prod.fst hh).symm.trans (congrArg Prod.snd hh)
    · intro hab
      subst b
      exact ⟨a,rfl⟩
  simp only [embeddedMatrixIdentityPoint, hdiag]

theorem embeddedMatrixIdentityPoint_bound (e : Fin n × Fin n ↪ Fin N) (k : Fin N) :
    |embeddedMatrixIdentityPoint e k| ≤ 1 := by
  unfold embeddedMatrixIdentityPoint
  split_ifs <;> norm_num

theorem embeddedMatrixDeterminantPolynomial_eval
    (e : Fin n × Fin n ↪ Fin N) (x : Fin N → ℝ) :
    MvPolynomial.eval x (embeddedMatrixDeterminantPolynomial e) =
      Matrix.det (fun i j : Fin n => x (e (i,j))) :=
  coordinateMatrixPolynomial_eval _ _

theorem embeddedMatrixDeterminantPolynomial_degree
    (e : Fin n × Fin n ↪ Fin N) (k : Fin N) :
    (embeddedMatrixDeterminantPolynomial e).degreeOf k ≤ n := by
  simpa only [Fintype.card_fin, embeddedMatrixDeterminantPolynomial] using
    coordinateMatrixPolynomial_degree (fun i j => e (i,j)) k

theorem embeddedMatrixDeterminantPolynomial_identity
    (e : Fin n × Fin n ↪ Fin N) :
    MvPolynomial.eval (embeddedMatrixIdentityPoint e) (embeddedMatrixDeterminantPolynomial e) = 1 := by
  rw [embeddedMatrixDeterminantPolynomial_eval]
  have he : (fun i j : Fin n => embeddedMatrixIdentityPoint e (e (i,j))) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simpa only [Matrix.one_apply] using embeddedMatrixIdentityPoint_entry e i j
  rw [he, Matrix.det_one]

noncomputable def embeddedMatrixDeterminantLip (n N : ℕ) : ℝ :=
  (N : ℝ) * ((n.factorial : ℝ) * ((n : ℝ) * 2 ^ n))

theorem embeddedMatrixDeterminantLip_nonneg (n N : ℕ) :
    0 ≤ embeddedMatrixDeterminantLip n N := by
  unfold embeddedMatrixDeterminantLip
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitTestClipping
namespace OAI

section

namespace Erdos3

open MeasureTheory

def unitTestClip (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem unitTestClip_mem (x : ℝ) : unitTestClip x ∈ Set.Icc (-1 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientSource
namespace OAI

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

theorem finiteProductMarginal_measurePreserving {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (μ : I → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (e : J → I) (he : Function.Injective e) :
    MeasurePreserving (fun x : I → X => fun j => x (e j))
      (Measure.pi μ) (Measure.pi (fun j => μ (e j))) := by
  have hind : iIndepFun (fun i (x : I → X) => x i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hsel := iIndepFun.precomp he hind
  have hm := hsel.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)
  refine ⟨by fun_prop, hm.trans ?_⟩
  congr 1
  funext j
  exact (measurePreserving_eval μ (e j)).map_eq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LargestBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def smallPrimePowerCorrection (Qs : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range Qs).filter Nat.Prime, p ^ Nat.log p (Qs - 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

noncomputable def integerScalarCubeDensityCap (I : Type*) [Fintype I] : ℝ :=
  (4 * (Fintype.card I + 1 : ℕ) : ℝ) ^ (Fintype.card I + 1)


open scoped BigOperators Classical

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSublevelThresholdBudget
namespace OAI


namespace Erdos3

noncomputable def polynomialSublevelThreshold (n m : ℕ) (C scale η : ℝ) : ℝ :=
  (2 * (1 + scale) * (1 + 2 * C * (m + 1 : ℝ) / η) ^ n)⁻¹

theorem polynomialSublevelThreshold_pos (n m : ℕ) {C scale η : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    0 < polynomialSublevelThreshold n m C scale η := by
  unfold polynomialSublevelThreshold
  positivity

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiscreteMinorThreshold
namespace OAI


namespace Erdos3


noncomputable def discreteScalarMinorThreshold (I J : Type*) [Fintype I] [Fintype J]
    (N : ℕ) (η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * Fintype.card I) 1
    ((integerScalarCubeDensityCap I) ^ Fintype.card J * multivariateSublevelConstant N (Fintype.card I))
    ((Fintype.card I + 1 : ℝ) ^ N) η

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointKernelCutoffBudget
namespace OAI


namespace Erdos3

noncomputable def jointKernelCutoff (n b : ℕ) (K T ε κ : ℝ) : ℕ :=
  ⌈1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε⌉₊

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3

noncomputable def scalarKernelTailConstant (I J : Type*) [Fintype I] [Fintype J] : ℝ :=
  (integerScalarCubeDensityCap I * (1 + ((Fintype.card I).factorial : ℝ))) ^ Fintype.card J


theorem univariateSublevelConstant_le_exp (q : ℕ) (hq : 0 < q) :
    univariateSublevelConstant q ≤ Real.exp ((q + 1 : ℝ) + q * (8 + (q + 1 : ℝ))) := by
  have hn : (q + 1 : ℝ) ≤ Real.exp (q + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (q + 1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hbase : 1 ≤ (q + 1 : ℝ) * (8 * (q + 1 : ℝ)) ^ q := by
    have hp : 1 ≤ (8 * (q + 1 : ℝ)) ^ q := one_le_pow₀ (by have := Nat.cast_nonneg q (α := ℝ); linarith)
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hi : (q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
  have hm : 8 * (q + 1 : ℝ) ≤ Real.exp (8 + (q + 1 : ℝ)) := by
    rw [Real.exp_add]
    exact mul_le_mul h8 hn (by positivity) (Real.exp_pos _).le
  calc
    _ ≤ (q + 1 : ℝ) * (8 * (q + 1 : ℝ)) ^ q := by
      simpa only [univariateSublevelConstant, Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hbase hi
    _ ≤ Real.exp (q + 1 : ℝ) * Real.exp (8 + (q + 1 : ℝ)) ^ q := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

theorem multivariateSublevelConstant_le_exp (N q : ℕ) (hq : 0 < q) :
    multivariateSublevelConstant N q ≤
      Real.exp (3 * (N : ℝ) + (q + 1 : ℝ) + q * (8 + (q + 1 : ℝ))) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hN : (N : ℝ) ≤ Real.exp N := by linarith [Real.add_one_le_exp (N : ℝ)]
  have hu0 := (univariateSublevelConstant_pos q).le
  have hu := univariateSublevelConstant_le_exp q hq
  unfold multivariateSublevelConstant
  calc
    _ ≤ (Real.exp 2) ^ N * Real.exp N *
        Real.exp ((q + 1 : ℝ) + q * (8 + (q + 1 : ℝ))) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PivotDensitySupport
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def spatialKernelErrorConstant (j d : ℕ) (U R : ℝ) (K : ℝ≥0) : ℝ :=
  (j.factorial * U ^ j) * (2 * R) ^ d * K * U

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteExcessMassCap
namespace OAI

section

namespace Erdos3

theorem marginalCap_max_one_exp_bound {C p : ℝ} (hp : 0 ≤ p)
    (hC : C ≤ Real.exp p) :
    1 ≤ max 1 C ∧ max 1 C ≤ Real.exp p :=
  ⟨le_max_left _ _, max_le (Real.one_le_exp hp) hC⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexNormalizationError
namespace OAI

section

namespace Erdos3

theorem complex_normalization_error {M F : ℂ} {Z E ε D : ℝ}
    (hZ : 1 / 2 ≤ Z) (herror : ‖M - F‖ ≤ E)
    (hmass : |Z - 1| ≤ ε) (hcap : ‖F‖ ≤ D) :
    ‖M / (Z : ℂ) - F‖ ≤ 2 * E + 2 * D * ε := by
  have hZpos : 0 < Z := by linarith
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZpos.ne'
  have hE : 0 ≤ E := (norm_nonneg _).trans herror
  have hε : 0 ≤ ε := (abs_nonneg _).trans hmass
  have hD : 0 ≤ D := (norm_nonneg _).trans hcap
  have he : M / (Z : ℂ) - F = ((M - F) + F * (1 - (Z : ℂ))) / (Z : ℂ) := by
    field_simp
    ring
  rw [he, norm_div, Complex.norm_real, Real.norm_of_nonneg hZpos.le]
  have hz : ‖1 - (Z : ℂ)‖ ≤ ε := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [abs_sub_comm] using hmass
  have hn : ‖(M - F) + F * (1 - (Z : ℂ))‖ ≤ E + D * ε :=
    (norm_add_le _ _).trans (add_le_add herror (by
      rw [norm_mul]
      exact mul_le_mul hcap hz (norm_nonneg _) hD))
  calc
    _ ≤ (E + D * ε) / Z := div_le_div_of_nonneg_right hn hZpos.le
    _ ≤ 2 * E + 2 * D * ε := (div_le_iff₀ hZpos).mpr (by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * Z - 1) (by positivity : 0 ≤ E + D * ε)])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.EarlyFiberCapBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def earlyFiberCapLog (P : ℝ) : ℝ := 3 * P ^ 3 + 17 * P ^ 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem pmf_interval_toReal_mass (L : ℕ) (p : PMF ℤ)
    (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ)) :
    (∑ k ∈ Finset.Ico 0 (L : ℤ), (p k).toReal) = 1 := by
  have hm : (∑ k ∈ Finset.Ico 0 (L : ℤ), p k) = 1 := by
    rw [← p.tsum_coe]
    apply (tsum_eq_sum (s := Finset.Ico 0 (L : ℤ)) _).symm
    intro k hk
    by_contra hn
    exact hk (hs k hn)
  rw [← ENNReal.toReal_sum (fun k _ => p.apply_ne_top k), hm, ENNReal.toReal_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def principalIntervalLength (K T γ : ℝ) : ℕ :=
  Nat.ceil (2 * γ * (K / T))

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)

include hK hT hγ in
theorem principalIntervalLength_pos : 0 < principalIntervalLength K T γ := by
  apply Nat.ceil_pos.mpr
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ModeAmplitudeErrorBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def modeAmplitudeAccuracy (L ε : ℝ) : ℝ := ε / (2 * (L + 1))

theorem modeAmplitudeAccuracy_pos {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    0 < modeAmplitudeAccuracy L ε := by
  unfold modeAmplitudeAccuracy
  positivity

theorem modeAmplitudeAccuracy_inv_le_exp {P L ε : ℝ}
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hLP : L ≤ Real.exp P)
    (hε : 0 < ε) (hεP : 1 / ε ≤ Real.exp P) :
    1 / modeAmplitudeAccuracy L ε ≤ Real.exp (2 * P + 2) := by
  have hden : 0 < L + 1 := by linarith
  have hone : 1 ≤ Real.exp P := Real.one_le_exp hP
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      4 = 2 * 2 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 := mul_le_mul htwo htwo (by norm_num) (Real.exp_nonneg 1)
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hinv : 1 / modeAmplitudeAccuracy L ε = 2 * (L + 1) * (1 / ε) := by
    unfold modeAmplitudeAccuracy
    field_simp
  rw [hinv]
  calc
    _ ≤ 4 * Real.exp P * Real.exp P := by
      have hfactor : 2 * (L + 1) ≤ 4 * Real.exp P := by linarith
      exact mul_le_mul hfactor hεP (by positivity) (by positivity)
    _ ≤ Real.exp 2 * Real.exp P * Real.exp P := by gcongr
    _ = Real.exp (2 * P + 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityIntegralBound
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem density_mul_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (D : X → ℝ) (hD : Integrable D μ) (f : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    Integrable (fun x => (D x : ℂ) * f x) μ :=
  hD.ofReal.mul_bdd hf (ae_of_all μ hbound)

theorem norm_density_integral_le_one {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (D : X → ℝ) (hD : Integrable D μ) (hD0 : ∀ x, 0 ≤ D x)
    (hDmass : (∫ x, D x ∂μ) = 1) (f : X → ℂ) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    ‖∫ x, (D x : ℂ) * f x ∂μ‖ ≤ 1 := by
  rw [← hDmass]
  apply norm_integral_le_of_norm_le hD
  apply ae_of_all
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hD0 x)]
  exact mul_le_of_le_one_right (hD0 x) (hbound x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

section

namespace Erdos3

noncomputable def quantitativeBadPrimeRadius (E : ℝ) : ℕ := ⌈4 * Real.exp E⌉₊ + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PatchTopNetBudget
namespace OAI

section

namespace Erdos3

noncomputable def patchTopNetNumerator (d s : ℕ) (M : ℝ) : ℝ :=
  ((s + 1) * (d + 1) ^ s : ℕ) * 4 * (1 + M) * ((1 + M) ^ (s * d)) ^ s

def patchTopNetNumeratorLog (s : ℕ) (p : ℝ) : ℝ :=
  s + s * p + p + 4 + s * s * p * (p + 1)

theorem patchTopNetNumeratorLog_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ patchTopNetNumeratorLog s p := by unfold patchTopNetNumeratorLog; positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedFixedPatchFunction
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exp_neg_le_div {P a b D : ℝ} (hD : 0 < D)
    (hDb : D ≤ Real.exp b) (hP : a + b ≤ P) :
    Real.exp (-P) ≤ Real.exp (-a) / D := by
  apply (le_div_iff₀ hD).mpr
  calc
    _ ≤ Real.exp (-P) * Real.exp b := mul_le_mul_of_nonneg_left hDb (Real.exp_nonneg _)
    _ = Real.exp (-P + b) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeLocalPivotVerticalBudget
namespace OAI

section

namespace Erdos3

theorem nativeLocalPivotVertical_inverse_precision_le_exp
    {pLocal r q : ℝ} (hbudget : pLocal + r + 1 ≤ q) :
    (Real.exp (-pLocal) * Real.exp (-r) / 2)⁻¹ ≤ Real.exp q := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hinv : (Real.exp (-pLocal) * Real.exp (-r) / 2)⁻¹ =
      2 * Real.exp (pLocal + r) := by
    rw [← Real.exp_add, ← neg_add, Real.exp_neg]
    simp [div_eq_mul_inv, mul_comm]
  rw [hinv]
  calc
    2 * Real.exp (pLocal + r) ≤ Real.exp 1 * Real.exp (pLocal + r) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (1 + (pLocal + r)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp q := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeLocalPivotVerticalPartners
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem norm_expect_scaled_product {T : Type*} (S : Finset T)
    (c : ℝ) (hc : 0 ≤ c) (f g : T → ℂ) :
    ‖𝔼 t ∈ S, ((c : ℂ) * f t) * g t‖ = c * ‖𝔼 t ∈ S, f t * g t‖ := by
  have he : (𝔼 t ∈ S, ((c : ℂ) * f t) * g t) =
      (c : ℂ) * (𝔼 t ∈ S, f t * g t) := by
    simp only [mul_assoc, Finset.mul_expect]
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSpatialChoiceBudget
namespace OAI

section

namespace Erdos3

noncomputable def normalizedSpatialShare (E : ℝ) : ℝ := Real.exp (-(E + 2))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CoordinateZeroProjection
namespace OAI

section

namespace Erdos3

open scoped ContDiff

variable {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P]

def coordinateZeroProjection (v : D → ℝ) : D → ℝ := fun d => if P d then 0 else v d

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedMaskedFactorBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

abbrev MaskedSiteResidueIndex (n : Fin m → ℕ) (E : Fin m → Type*) :=
  (Σ j, Fin (n j)) ⊕ (Σ j, E j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

abbrev EnlargedPreparedCommonKernel (m Jalloc : ℕ) :=
  Fin ((m + 1) * (m + 3) + (m + 1) * Jalloc)

theorem enlargedPreparedCommonKernel_analytic_capacity (m Jalloc s : ℕ) (hs : s ≤ m) :
    (s + 1) * (s + 3) ≤ Fintype.card (EnlargedPreparedCommonKernel m Jalloc) := by
  simp only [EnlargedPreparedCommonKernel, Fintype.card_fin]
  exact (Nat.mul_le_mul (by omega) (by omega)).trans (Nat.le_add_right _ _)

def enlargedPreparedCommonCanonicalSelection (m Jalloc s : ℕ) (hs : s ≤ m) :
    Fin (s + 1) ↪ EnlargedPreparedCommonKernel m Jalloc where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt (by
    have hcap := enlargedPreparedCommonKernel_analytic_capacity m Jalloc s hs
    have hsmall : s + 1 ≤ (s + 1) * (s + 3) := by nlinarith
    simpa only [EnlargedPreparedCommonKernel, Fintype.card_fin] using hsmall.trans hcap)⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun z : EnlargedPreparedCommonKernel m Jalloc => z.val) h)

@[simp] theorem enlargedPreparedCommonCanonicalSelection_val (m Jalloc s : ℕ)
    (hs : s ≤ m) (i : Fin (s + 1)) :
    (enlargedPreparedCommonCanonicalSelection m Jalloc s hs i).val = i.val := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalBadProductErrorBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def physicalBadProductAccuracy (E Vlog : ℝ) : ℝ :=
  Real.exp (-(Vlog + 3 * E + 16))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def modularRankSmallBallExponent (s : ℕ) : ℝ := (2 : ℝ) ^ (1 - (s : ℝ))

end Erdos3

end

section

namespace Erdos3

def modularInitialRankStrength (s d : ℕ) : ℕ :=
  2 ^ (2 * s) * s.factorial * (d + 2)

def modularInitialBlockCount (s d : ℕ) : ℕ :=
  2 ^ s * (modularInitialRankStrength s d + d + 10) + 1

theorem modularInitialBlockCount_linear_bound (s d : ℕ) :
    modularInitialBlockCount s d ≤
      (2 ^ s * (2 ^ (2 * s) * s.factorial + 1) + 1) * (d + 11) := by
  dsimp only [modularInitialBlockCount, modularInitialRankStrength]
  nlinarith [Nat.zero_le (2 ^ s), Nat.zero_le (2 ^ (2 * s) * s.factorial)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

section TopPart

variable {I J R : Type*} [CommRing R]

theorem homogeneousComponent_killCompl (f : J → I) (hf : Function.Injective f)
    (P : MvPolynomial I R) (r : ℕ) :
    homogeneousComponent r (killCompl hf P) = killCompl hf (homogeneousComponent r P) := by
  ext a
  simp only [coeff_homogeneousComponent, coeff_killCompl, Finsupp.degree_mapDomain]

end TopPart

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedSmoothPolynomialSublevel
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

noncomputable def shiftedSmoothSublevelConstant (N d : ℕ) : ℝ :=
  (2 : ℝ) ^ N * (2 ^ N * multivariateSublevelConstant N d)

noncomputable def shiftedSmoothSublevelThreshold (N d count : ℕ) (η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * d) count (shiftedSmoothSublevelConstant N d)
    ((d + 1 : ℝ) ^ N) η

theorem shiftedSmoothSublevelConstant_nonneg {N : ℕ} (hN : 0 < N) (d : ℕ) :
    0 ≤ shiftedSmoothSublevelConstant N d := by
  unfold shiftedSmoothSublevelConstant
  exact mul_nonneg (by positivity)
    (mul_nonneg (by positivity) (multivariateSublevelConstant_pos hN d).le)

theorem shiftedSmoothSublevelThreshold_pos {N : ℕ} (hN : 0 < N) (d count : ℕ)
    {η : ℝ} (hη : 0 < η) : 0 < shiftedSmoothSublevelThreshold N d count η :=
  polynomialSublevelThreshold_pos _ _ (shiftedSmoothSublevelConstant_nonneg hN d)
    (by positivity) hη

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SmoothMatrixBlockBudget
namespace OAI

section

namespace Erdos3

noncomputable def smoothMatrixBlockMesh (n N : ℕ) (κ : ℝ) : ℝ :=
  min 1 (κ / (embeddedMatrixDeterminantLip n N + 1))

theorem smoothMatrixBlockMesh_spec (n N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < smoothMatrixBlockMesh n N κ ∧ smoothMatrixBlockMesh n N κ ≤ 1 ∧
      embeddedMatrixDeterminantLip n N * smoothMatrixBlockMesh n N κ ≤ κ := by
  have hK := embeddedMatrixDeterminantLip_nonneg n N
  have hK1 : 0 < embeddedMatrixDeterminantLip n N + 1 := by positivity
  have hδ : 0 < smoothMatrixBlockMesh n N κ :=
    lt_min (by norm_num) (div_pos hκ hK1)
  have hmul : smoothMatrixBlockMesh n N κ * (embeddedMatrixDeterminantLip n N + 1) ≤ κ :=
    (le_div_iff₀ hK1).mp (min_le_right 1 (κ / (embeddedMatrixDeterminantLip n N + 1)))
  refine ⟨hδ, min_le_left _ _, ?_⟩
  nlinarith

end Erdos3

end

section

namespace Erdos3
open scoped Classical

noncomputable def smoothMatrixBlockConstantLogBudget (N n : ℕ) : ℝ :=
  5 * (N : ℝ) + (n + 1 : ℝ) + n * (8 + (n + 1 : ℝ))

noncomputable def smoothMatrixBlockThresholdLogBudget (N n count : ℕ) (E : ℝ) : ℝ :=
  (N : ℝ) * n + 2 + ((N * n : ℕ) : ℝ) *
    (smoothMatrixBlockConstantLogBudget N n + count + E + 2)

theorem smoothMatrixBlockConstantLogBudget_nonneg (N n : ℕ) :
    0 ≤ smoothMatrixBlockConstantLogBudget N n := by
  unfold smoothMatrixBlockConstantLogBudget
  positivity

theorem smoothMatrixBlockThresholdLogBudget_nonneg (N n count : ℕ)
    {E : ℝ} (hE : 0 ≤ E) : 0 ≤ smoothMatrixBlockThresholdLogBudget N n count E := by
  unfold smoothMatrixBlockThresholdLogBudget
  have := smoothMatrixBlockConstantLogBudget_nonneg N n
  positivity

theorem shiftedSmoothSublevelConstant_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) :
    shiftedSmoothSublevelConstant N n ≤ Real.exp (smoothMatrixBlockConstantLogBudget N n) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hmulti := multivariateSublevelConstant_le_exp N n hn
  have hmulti0 := (multivariateSublevelConstant_pos hN n).le
  unfold shiftedSmoothSublevelConstant smoothMatrixBlockConstantLogBudget
  calc
    _ ≤ (Real.exp 1) ^ N * ((Real.exp 1) ^ N *
        Real.exp (3 * (N : ℝ) + (n + 1 : ℝ) + n * (8 + (n + 1 : ℝ)))) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem smoothMatrixBlock_scale_le_exp (N n : ℕ) :
    (n + 1 : ℝ) ^ N ≤ Real.exp ((N : ℝ) * n) := by
  have hb : (n + 1 : ℝ) ≤ Real.exp (n : ℝ) := Real.add_one_le_exp _
  calc
    _ ≤ (Real.exp (n : ℝ)) ^ N := pow_le_pow_left₀ (by positivity) hb N
    _ = _ := (Real.exp_nat_mul (n : ℝ) N).symm

noncomputable def smoothMatrixBlockMeshLogBudget (N n count : ℕ) (E : ℝ) : ℝ :=
  smoothMatrixBlockThresholdLogBudget N n count E +
    ((N : ℝ) + (n : ℝ) ^ 2 + 2 * n) + 1

theorem smoothMatrixBlockMeshLogBudget_nonneg (N n count : ℕ)
    {E : ℝ} (hE : 0 ≤ E) : 0 ≤ smoothMatrixBlockMeshLogBudget N n count E := by
  unfold smoothMatrixBlockMeshLogBudget
  have := smoothMatrixBlockThresholdLogBudget_nonneg N n count hE
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem spatialMatrix_decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

noncomputable def spatialMatrixBlockThreshold (n : ℕ) (η : ℝ) : ℝ :=
  shiftedSmoothSublevelThreshold (2 * n * n) n 2 η

theorem spatialMatrixBlockThreshold_pos {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    0 < spatialMatrixBlockThreshold n η :=
  shiftedSmoothSublevelThreshold_pos (by positivity) n 2 hη

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ModularCoefficientBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def modularCoefficientPrimeThreshold (s : ℕ) : ℕ :=
  max 2 ⌈(s : ℝ) ^ (4 / modularRankSmallBallExponent s)⌉₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastRawSpatialBoxReorder
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (n : Fin m → ℕ) (N : ℕ) [NeZero N]

abbrev ForecastSingleDeckResidues (E : Fin m → Type*) (N : ℕ) :=
  ∀ j, Unit → E j → ZMod N

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedCenteredBadPrimeSurrogate
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (rankC : ℝ)

theorem singleton_prime_neZero (p : ℕ) [NeZero p] (r : ({p} : Finset ℕ)) : NeZero r.val := by
  have hr : r.val = p := Finset.mem_singleton.mp r.property
  rw [hr]
  infer_instance

theorem singleton_prime_power_dvd (p a : ℕ) (r : ({p} : Finset ℕ)) : r.val ^ a ∣ p ^ a := by
  have hr : r.val = p := Finset.mem_singleton.mp r.property
  simp only [hr, dvd_refl]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarBadSublevelRamp
namespace OAI

section

namespace Erdos3
open scoped NNReal

noncomputable def scalarBadSublevelRamp (κ t : ℝ) : ℝ :=
  max 0 (min 1 (2 - 2 * |t| / κ))

theorem scalarBadSublevelRamp_range (κ t : ℝ) :
    scalarBadSublevelRamp κ t ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem scalarBadSublevelRamp_eq_one {κ t : ℝ} (hκ : 0 < κ) (ht : |t| ≤ κ / 2) :
    scalarBadSublevelRamp κ t = 1 := by
  have hr : 2 * |t| / κ ≤ 1 := (div_le_one hκ).mpr (by linarith)
  rw [scalarBadSublevelRamp, min_eq_left (by linarith), max_eq_right zero_le_one]

theorem scalarBadSublevelRamp_eq_zero {κ t : ℝ} (hκ : 0 < κ) (ht : κ ≤ |t|) :
    scalarBadSublevelRamp κ t = 0 := by
  have hr : 2 ≤ 2 * |t| / κ := (le_div_iff₀ hκ).mpr (by linarith)
  rw [scalarBadSublevelRamp, min_eq_right (by linarith), max_eq_left (by linarith)]

theorem scalarBadSublevelRamp_lipschitz {κ : ℝ} (hκ : 0 < κ) :
    LipschitzWith ⟨2 / κ, by positivity⟩ (scalarBadSublevelRamp κ) := by
  have hraw : LipschitzWith ⟨2 / κ, by positivity⟩ (fun t : ℝ => 2 - 2 * |t| / κ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq]
    have he : (2 - 2 * |x| / κ) - (2 - 2 * |y| / κ) = -(2 / κ) * (|x| - |y|) := by ring
    rw [he, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 / κ)]
    exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) (by positivity)
  exact (hraw.const_min 1).const_max 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitBoundProductDifference
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem norm_finset_prod_sub_prod_le_sum {ι A : Type*}
    [NormedCommRing A] [NormOneClass A]
    (s : Finset ι) (f g : ι → A)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfs : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hprod : ‖∏ i ∈ s, f i‖ ≤ 1 :=
      (s.norm_prod_le f).trans (Finset.prod_le_one (fun i _ => norm_nonneg (f i)) hfs)
    have hga : ‖g a‖ ≤ 1 := hg a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      ‖f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i)‖ =
          ‖(f a - g a) * (∏ i ∈ s, f i) +
            g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := by congr 1; ring
      _ ≤ ‖(f a - g a) * (∏ i ∈ s, f i)‖ +
          ‖g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := norm_add_le _ _
      _ ≤ ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ +
          ‖g a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖f a - g a‖ * 1 + 1 * (∑ i ∈ s, ‖f i - g i‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
          (mul_le_mul hga (ih hfs hgs) (norm_nonneg _) (by norm_num))
      _ = ‖f a - g a‖ + ∑ i ∈ s, ‖f i - g i‖ := by simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedDeterminantCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem unitTestClip_lipschitz : LipschitzWith 1 unitTestClip :=
  (LipschitzWith.id.const_min 1).const_max (-1)

theorem unitTestClip_eq_self {x : ℝ} (hx : |x| ≤ 1) : unitTestClip x = x := by
  rcases abs_le.mp hx with ⟨hl, hu⟩
  simp only [unitTestClip, min_eq_right hu, max_eq_right hl]

theorem unitTestClip_norm_le_one (x : ℝ) : ‖unitTestClip x‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using unitTestClip_mem x

noncomputable def clippedSelectedDeterminant {A : Type*} (n : ℕ)
    (coords : Fin n → Fin n → A) (x : A → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun i j => unitTestClip (x (coords i j))))

theorem real_perm_sign_norm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ‖((Equiv.Perm.sign σ : ℤ) : ℝ)‖ = 1 := by
  rw [Real.norm_eq_abs, ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]

theorem clippedSelectedDeterminant_lipschitz {A : Type*} [Fintype A]
    (n : ℕ) (coords : Fin n → Fin n → A) :
    LipschitzWith ((n * n.factorial : ℕ) : ℝ≥0) (clippedSelectedDeterminant n coords) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hprod (σ : Equiv.Perm (Fin n)) :
      ‖(∏ i, unitTestClip (x (coords (σ i) i))) -
        ∏ i, unitTestClip (y (coords (σ i) i))‖ ≤ (n : ℝ) * dist x y := by
    calc
      _ ≤ ∑ i : Fin n, ‖unitTestClip (x (coords (σ i) i)) -
          unitTestClip (y (coords (σ i) i))‖ :=
        VectorPolynomial.norm_finset_prod_sub_prod_le_sum Finset.univ _ _
          (fun i _ => unitTestClip_norm_le_one _) (fun i _ => unitTestClip_norm_le_one _)
      _ ≤ ∑ _i : Fin n, dist x y := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← dist_eq_norm]
        exact (unitTestClip_lipschitz.dist_le_mul _ _).trans (by
          simpa using dist_le_pi_dist x y (coords (σ i) i))
      _ = (n : ℝ) * dist x y := by simp
  rw [dist_eq_norm, clippedSelectedDeterminant, clippedSelectedDeterminant,
    Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n),
        ‖((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i, unitTestClip (x (coords (σ i) i))) -
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i, unitTestClip (y (coords (σ i) i)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), (n : ℝ) * dist x y := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [← mul_sub, norm_mul, real_perm_sign_norm, one_mul]
      exact hprod σ
    _ = ↑((n * n.factorial : ℕ) : ℝ≥0) * dist x y := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, NNReal.coe_mul, NNReal.coe_natCast]
      ring

end Erdos3

end

section

namespace Erdos3
open scoped NNReal Classical

noncomputable def normalizedDeterminantCutoff {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) (κ : ℝ) (x : A → ℝ) : ℝ :=
  max (scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords 0) x))
    (scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords 1) x))

theorem normalizedDeterminantCutoff_range {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) (κ : ℝ) (x : A → ℝ) :
    normalizedDeterminantCutoff n coords κ x ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨(scalarBadSublevelRamp_range κ _).1.trans (le_max_left _ _),
    max_le (scalarBadSublevelRamp_range κ _).2 (scalarBadSublevelRamp_range κ _).2⟩

theorem normalizedDeterminantCutoff_lipschitz {A : Type*} [Fintype A] (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ) :
    LipschitzWith (⟨2 / κ, by positivity⟩ * ((n * n.factorial : ℕ) : ℝ≥0))
      (normalizedDeterminantCutoff n coords κ) := by
  unfold normalizedDeterminantCutoff
  have h (b : Fin 2) := (scalarBadSublevelRamp_lipschitz hκ).comp
    (clippedSelectedDeterminant_lipschitz n (coords b))
  simpa only [max_self, Function.comp_def] using (h 0).max (h 1)

theorem normalizedDeterminantCutoff_eq_one {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ)
    (x : A → ℝ) (hx : ∀ b i j, |x (coords b i j)| ≤ 1)
    (hbad : ∃ b : Fin 2, |Matrix.det (fun i j => x (coords b i j))| ≤ κ / 2) :
    normalizedDeterminantCutoff n coords κ x = 1 := by
  obtain ⟨b, hb⟩ := hbad
  have he : clippedSelectedDeterminant n (coords b) x = Matrix.det (fun i j => x (coords b i j)) := by
    unfold clippedSelectedDeterminant
    congr 1
    funext i j
    exact unitTestClip_eq_self (hx b i j)
  have hb1 : scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords b) x) = 1 :=
    scalarBadSublevelRamp_eq_one hκ (by rw [he]; exact hb)
  apply le_antisymm (normalizedDeterminantCutoff_range n coords κ x).2
  fin_cases b
  · exact hb1 ▸ le_max_left _ _
  · exact hb1 ▸ le_max_right _ _

theorem normalizedDeterminantCutoff_eq_zero {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ)
    (x : A → ℝ) (hx : ∀ b i j, |x (coords b i j)| ≤ 1)
    (hgood : ∀ b : Fin 2, κ ≤ |Matrix.det (fun i j => x (coords b i j))|) :
    normalizedDeterminantCutoff n coords κ x = 0 := by
  have he (b : Fin 2) : clippedSelectedDeterminant n (coords b) x =
      Matrix.det (fun i j => x (coords b i j)) := by
    unfold clippedSelectedDeterminant
    congr 1
    funext i j
    exact unitTestClip_eq_self (hx b i j)
  have hz (b : Fin 2) : scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords b) x) = 0 :=
    scalarBadSublevelRamp_eq_zero hκ (by rw [he]; exact hgood b)
  simp only [normalizedDeterminantCutoff, hz, max_self]

theorem normalizedDeterminantCutoff_indicator_bounds {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ)
    (x : A → ℝ) (hx : ∀ b i j, |x (coords b i j)| ≤ 1) :
    (if ∃ b : Fin 2, |Matrix.det (fun i j => x (coords b i j))| ≤ κ / 2 then (1 : ℝ) else 0) ≤
      normalizedDeterminantCutoff n coords κ x ∧
    normalizedDeterminantCutoff n coords κ x ≤
      (if ∃ b : Fin 2, |Matrix.det (fun i j => x (coords b i j))| ≤ κ then (1 : ℝ) else 0) := by
  constructor
  · split_ifs with hbad
    · exact (normalizedDeterminantCutoff_eq_one n coords hκ x hx hbad).ge
    · exact (normalizedDeterminantCutoff_range n coords κ x).1
  · split_ifs with hbad
    · exact (normalizedDeterminantCutoff_range n coords κ x).2
    · exact (normalizedDeterminantCutoff_eq_zero n coords hκ x hx
        (fun b => le_of_lt (lt_of_not_ge (fun h => hbad ⟨b,h⟩)))).le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointExceptionalGainBudget
namespace OAI

section

namespace Erdos3

noncomputable def jointSpatialError (gainLog : ℝ) : ℝ :=
  Real.exp (-gainLog) / 128

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankPreparedBlocks
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

def enlargedPreparedRankSpatialEmbedding (m Jalloc J : ℕ) (hJ : J ≤ Jalloc) :
    Fin J ↪ EnlargedPreparedCommonKernel m Jalloc :=
  (Fin.castLEEmb (hJ.trans (by nlinarith : Jalloc ≤ (m + 1) * Jalloc))).trans
    (Fin.natAddEmb ((m + 1) * (m + 3)))

def enlargedPreparedRankKernelEmbedding (m Jalloc J : ℕ) (hJ : J ≤ Jalloc) (j : Fin m) :
    Fin J × Fin (j.val + 1) ↪ EnlargedPreparedCommonKernel m Jalloc :=
  (finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (by
    calc
      J * (j.val + 1) ≤ Jalloc * (m + 1) := Nat.mul_le_mul hJ (by omega)
      _ = (m + 1) * Jalloc := Nat.mul_comm _ _))).trans
    (Fin.natAddEmb ((m + 1) * (m + 3)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedEnlargedModularAllocation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {X₀ J₀ : Type}
  {m : ℕ}

def preparedInitialRankSpatialEmbedding (nX M : ℕ) :
    Fin (modularInitialBlockCount m (nX + m * M)) ↪
      EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) :=
  enlargedPreparedRankSpatialEmbedding m _ _ le_rfl

def preparedInitialRankKernelEmbedding (nX M : ℕ) (j : Fin m) :
    Fin (modularInitialBlockCount m (nX + m * M)) × Fin (j.val + 1) ↪
      EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) :=
  enlargedPreparedRankKernelEmbedding m _ _ le_rfl j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalZeroLayerBudgetedInitialization
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical TensorProduct NNReal

namespace CanonicalEmptyLayerGeometry

theorem zeroLayer_one_pos (j : Fin 0) : (0 : ℝ) < 1 := Fin.elim0 j

end CanonicalEmptyLayerGeometry

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardFrontProfileBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardFrontProfile_slice_bound (Cslice : ℕ)
    {x p : ℝ} (hCslice : 1 ≤ Cslice) (hx : 0 ≤ x) (hp : p ≤ x) :
    p ≤ (x + Cslice) ^ Cslice := by
  have hC : (1 : ℝ) ≤ Cslice := by exact_mod_cast hCslice
  have hbase : 1 ≤ x + Cslice := by linarith only [hx, hC]
  apply hp.trans
  apply (le_add_of_nonneg_right (Nat.cast_nonneg Cslice)).trans
  simpa only [pow_one] using pow_le_pow_right₀ hbase hCslice

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedFiniteScheduleDirectCoarse {K : Type*} [Fintype K]
    (gainLog : K → ℝ) (requestedCoarse : ℝ) : ℝ :=
  max (∑ k, (gainLog k + 32)) requestedCoarse

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedFiniteNestedSourceProjectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedFiniteForwardFrontProjectionPrecision (u p native : ℝ) : ℝ :=
  u + 2 * p + max (max native 3) (2 * u + 4 * p + 20) + 32

theorem preparedFiniteForwardFrontProjectionPrecision_nonneg
    {u p native : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    0 ≤ preparedFiniteForwardFrontProjectionPrecision u p native := by
  have hmax : 2 * u + 4 * p + 20 ≤ max (max native 3) (2 * u + 4 * p + 20) :=
    le_max_right _ _
  unfold preparedFiniteForwardFrontProjectionPrecision
  linarith only [hu, hp, hmax]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedGeometryConditionalExcess
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX s : ℕ}
  {G : Type}
  [Fintype G]
  [DecidableEq G]
  {I : Fin m → Type}
  [∀ j, Fintype (I j)]
  {n : Fin m → ℕ}
  {J : Fin m → Type}
  [∀ j, Fintype (J j)]
  {U : ∀ j, Submodule ℝ (J j → ℝ)}
  {R σ : Fin m → ℝ}
  {hR : ∀ j, 0 < R j}
  {hσ : ∀ j, 0 < σ j}
  {N : Fin nX → ℕ}
  {τ ξ : ℝ}
  {stride : Fin nX → ℕ}

namespace AllocatedExternalCandidateSamplerFamily

noncomputable local instance preparedConditionalExcessFinDecidableEq : DecidableEq (Fin nX) := Classical.decEq _

end AllocatedExternalCandidateSamplerFamily
end Erdos3.VectorPolynomial

end

end OAI
end


