-- Prove2me | Definitions.Def_OAIE3v2B039
-- name    : OAIE3v2B039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:12:55.923481+00:00
-- url     : https://prove2.me/theorems/d4d04cca-ab73-4ec9-97b3-c62797e699ea
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 40 of 311
-- statement:
--   Definitions bundle 40 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003` of this split.
--
--   Modules: `Estimates/CorrelationDerivative.lean`, `Estimates/FiniteFiberTest.lean`, `Estimates/LieFiniteProduct.lean`, `Estimates/PartialComplexScaledQuadrature.lean`, `Estimates/RationalHeight.lean`, `Estimates/RationalRowReduction.lean`, `Estimates/RealWeightPMF.lean`, `Estimates/SplitSmoothProductProfile.lean`, `Estimates/WeightedDerivationDrop.lean`, `Estimates/WeightedLoweringGroup.lean`, `Estimates/WeightedTranslationShearExponential.lean`, `Fourier/FiniteFourierSmoothing.lean`, `Fourier/RectangularGridCharacter.lean`, `Geometry/LieCoordinateHeight.lean`, `Geometry/LieCoordinateScalarExtension.lean`, `Geometry/LieCoordinateSmooth.lean`, `Geometry/WeightedSubstitutionSupport.lean`, `Geometry/WeightedSupportDropRename.lean`, `Lattices/IntegerAffineSubstitution.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/SelectedResidueApproximation.lean`, `Linear/BasisGradedCoordinateBasis.lean`, `Linear/RationalMatrixSeparation.lean`, `Linear/WeightedLieUpperSpan.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/LieBCHContinuity.lean`, `Nilpotent/NiltestAffineProjection.lean`, `Nilpotent/NiltestBasepointNormalization.lean`, `Polynomial/DegreeRankSunflower.lean`, `Polynomial/ExtendedPolynomialValues.lean`, `Polynomial/LieCoordinatePolynomials.lean`, `Polynomial/MajorWeightedDegreeTools.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Polynomial/PolynomialCoefficientNormalization.lean`, `Polynomial/PolynomialIntegerInputs.lean`, `Polynomial/PolynomialKernelValues.lean`, `Polynomial/PolynomialPatchProductBudget.lean`, `Polynomial/PolynomialShearAffineExponential.lean`, `Polynomial/PolynomialShearRationalFiltration.lean`, `Polynomial/PolynomialShearRealGroup.lean`, `Polynomial/PolynomialTranslationSeries.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Polynomial/WeightedLinearPolynomialRestriction.lean`, `Probability/FiniteConditionedMass.lean`, `Probability/FiniteDensityMassBound.lean`, `Probability/FiniteProbabilityLipschitz.lean`, `Probability/ShiftedSmoothProductLaw.lean`, `Sampling/RationalSpanGrid.lean`, `Sampling/RealGridSeparation.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

noncomputable def mean (f : Ω → ℝ) : ℝ := ∑ x, p.weight x * f x

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω H : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

noncomputable def complexMean (v : Ω → ℂ) : ℂ := ∑ x, (p.weight x : ℂ) * v x

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace FiniteProbabilityWeights

variable (p : FiniteProbabilityWeights Ω) (G : Finset Ω)

noncomputable def mass : ℝ := ∑ x ∈ G, p.weight x

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalHeight
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem RationalHeightLE.mono {q : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hHK : H ≤ K) : RationalHeightLE q K :=
  ⟨hq.1.trans hHK, hq.2.trans hHK⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
namespace OAI

section

namespace Erdos3

open PowerSeries

section Ring
variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem isNilpotent_nilpotentLog {a : A} (ha : IsNilpotent a) :
    IsNilpotent (nilpotentLog a) := by
  let S := Algebra.adjoin ℚ ({a} : Set A)
  let x : S := ⟨a, Algebra.self_mem_adjoin_singleton ℚ a⟩
  have hx : IsNilpotent x :=
    (IsNilpotent.map_iff (f := S.val) Subtype.val_injective).mp ha
  have h := (isNilpotent_nilpotentLog_comm hx).map S.val
  rwa [map_nilpotentLog hx S.val] at h

end Ring
end Erdos3

end

section

namespace Erdos3

open PowerSeries _root_.Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem nilpotentBCH_eq_add_of_commute {a b : A} (ha : IsNilpotent a)
    (hb : IsNilpotent b) (hab : Commute a b) : nilpotentBCH a b = a + b := by
  rw [nilpotentBCH, ← IsNilpotent.exp_add_of_commute hab ha hb,
    nilpotentLog_exp_sub_one (hab.isNilpotent_add ha hb)]

end Erdos3

end

section

namespace Erdos3

open IsNilpotent TensorProduct Module.End

variable {R M N P : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [Module ℚ M] [IsScalarTower ℚ R M]
  [AddCommGroup N] [Module R N] [Module ℚ N] [IsScalarTower ℚ R N]
  [AddCommGroup P] [Module R P] [Module ℚ P] [IsScalarTower ℚ R P]

theorem nilpotentLog_intertwine
    {DM : Module.End R M} {DN : Module.End R N} {g : M →ₗ[R] N}
    (hM : IsNilpotent DM) (hN : IsNilpotent DN) (h : DN ∘ₗ g = g ∘ₗ DM) :
    nilpotentLog DN ∘ₗ g = g ∘ₗ nilpotentLog DM := by
  ext x
  obtain ⟨k, hk⟩ := hM
  obtain ⟨l, hl⟩ := hN
  have hmk : DM ^ max k l = 0 := pow_eq_zero_of_le (le_max_left k l) hk
  have hnl : DN ^ max k l = 0 := pow_eq_zero_of_le (le_max_right k l) hl
  have hp (i : ℕ) : (DN ^ i) (g x) = g ((DM ^ i) x) := by
    simpa using LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h i) x
  simp [nilpotentLog_eq_sum hmk, nilpotentLog_eq_sum hnl, hp, map_rat_smul]

theorem nilpotentExp_intertwine_injective
    {DM : Module.End R M} {DN : Module.End R N} {g : M →ₗ[R] N}
    (hM : IsNilpotent DM) (hN : IsNilpotent DN)
    (h : exp DN ∘ₗ g = g ∘ₗ exp DM) : DN ∘ₗ g = g ∘ₗ DM := by
  have hd : (exp DN - 1) ∘ₗ g = g ∘ₗ (exp DM - 1) := by
    ext x
    have hx := LinearMap.congr_fun h x
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      using congrArg (fun y => y - g x) hx
  have hl := nilpotentLog_intertwine (isNilpotent_exp_sub_one hM)
    (isNilpotent_exp_sub_one hN) hd
  simpa only [nilpotentLog_exp_sub_one hM, nilpotentLog_exp_sub_one hN] using hl

omit [IsScalarTower ℚ R M] [IsScalarTower ℚ R N] in
theorem nilpotentExp_bilinear_injective
    (b : M →ₗ[R] N →ₗ[R] P)
    (DM : Module.End R M) (DN : Module.End R N) (DP : Module.End R P)
    (hM : IsNilpotent DM) (hN : IsNilpotent DN) (hP : IsNilpotent DP)
    (hb : ∀ x y, exp DP (b x y) = b (exp DM x) (exp DN y)) (x : M) (y : N) :
    DP (b x y) = b (DM x) y + b x (DN y) := by
  let DL : Module.End R (M ⊗[R] N) := DM.rTensor N
  let DR : Module.End R (M ⊗[R] N) := DN.lTensor M
  have hL : IsNilpotent DL := hM.map (rTensorAlgHom R M N)
  have hR : IsNilpotent DR := hN.map (lTensorAlgHom R N M)
  have hc : Commute DL DR := by ext; simp [DL, DR]
  let m : M ⊗[R] N →ₗ[R] P := TensorProduct.lift b
  have heL : exp DL = (exp DM).rTensor N := (hM.map_exp (rTensorAlgHom R M N)).symm
  have heR : exp DR = (exp DN).lTensor M := (hN.map_exp (lTensorAlgHom R N M)).symm
  have he : exp DP ∘ₗ m = m ∘ₗ exp (DL + DR) := by
    ext x y
    simp [m, exp_add_of_commute hc hL hR, heL, heR, hb]
  have hd := nilpotentExp_intertwine_injective (hc.isNilpotent_add hL hR) hP he
  simpa [m, DL, DR] using LinearMap.congr_fun hd (x ⊗ₜ[R] y)

theorem nilpotentLog_bilinear
    (b : M →ₗ[R] N →ₗ[R] P)
    (FM : Module.End R M) (FN : Module.End R N) (FP : Module.End R P)
    (hM : IsNilpotent (FM - 1)) (hN : IsNilpotent (FN - 1))
    (hP : IsNilpotent (FP - 1))
    (hb : ∀ x y, FP (b x y) = b (FM x) (FN y)) (x : M) (y : N) :
    nilpotentLog (FP - 1) (b x y) =
      b (nilpotentLog (FM - 1) x) y + b x (nilpotentLog (FN - 1) y) := by
  apply nilpotentExp_bilinear_injective b _ _ _
    (isNilpotent_nilpotentLog hM) (isNilpotent_nilpotentLog hN)
    (isNilpotent_nilpotentLog hP) _ x y
  simpa only [exp_nilpotentLog hM, exp_nilpotentLog hN, exp_nilpotentLog hP,
    show 1 + (FM - 1) = FM by abel,
    show 1 + (FN - 1) = FN by abel,
    show 1 + (FP - 1) = FP by abel] using hb

end Erdos3

end

section

namespace Erdos3

open Module

section General

variable {X Y L : Type*} [TopologicalSpace Y] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L]

omit [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L] in
theorem continuous_rightBracketList
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆))
    (f : X → Y → L) (hf : ∀ x, Continuous (f x)) (xs : List X)
    (a : Y → L) (ha : Continuous a) :
    Continuous (fun y => rightBracketList (fun x => f x y) xs (a y)) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih (fun y => ⁅a y, f x y⁆) (hlie.comp (ha.prodMk (hf x)))

omit [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L] in
theorem continuous_dynkinWord
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆))
    (f : X → Y → L) (hf : ∀ x, Continuous (f x)) (w : FreeSemigroup X) :
    Continuous (fun y => dynkinWord (fun x => f x y) w) :=
  continuous_rightBracketList hlie f hf w.tail (f w.head) (hf w.head)

end General

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Pointwise

variable {σ R : Type*} [CommRing R]

theorem weightedSupportLT_mul_LE {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w d) (hq : q ∈ weightedSupportLE w e) :
    p * q ∈ weightedSupportLT w (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  exact (map_add (Finsupp.weight w) β γ).trans_lt (Nat.add_lt_add_of_lt_of_le (hp hβ) (hq hγ))

theorem weightedSupportLE_mul_LT {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (hq : q ∈ weightedSupportLT w e) :
    p * q ∈ weightedSupportLT w (d + e) := by
  rw [mul_comm, Nat.add_comm]
  exact weightedSupportLT_mul_LE hq hp

theorem translation_bounds_mul (h : σ → R) (w : σ → ℕ)
    (p q : MvPolynomial σ R) (d e : ℕ)
    (hp : p ∈ weightedSupportLE w d)
    (htp : polynomialTranslate h p ∈ weightedSupportLE w d)
    (htq : polynomialTranslate h q ∈ weightedSupportLE w e)
    (hdp : polynomialTranslate h p - p ∈ weightedSupportLT w d)
    (hdq : polynomialTranslate h q - q ∈ weightedSupportLT w e) :
    polynomialTranslate h (p * q) ∈ weightedSupportLE w (d + e) ∧
      polynomialTranslate h (p * q) - p * q ∈ weightedSupportLT w (d + e) := by
  refine ⟨by rw [map_mul]; exact weightedSupportLE_mul htp htq, ?_⟩
  rw [map_mul, show polynomialTranslate h p * polynomialTranslate h q - p * q =
    (polynomialTranslate h p - p) * polynomialTranslate h q + p * (polynomialTranslate h q - q) by ring]
  exact (weightedSupportLT w (d + e)).add_mem (weightedSupportLT_mul_LE hdp htq)
    (weightedSupportLE_mul_LT hp hdq)

theorem polynomialTranslate_monomial_bounds (h : σ → R) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) ∈ weightedSupportLE w (Finsupp.weight w α) ∧
      polynomialTranslate h (monomial α 1) - monomial α 1 ∈
        weightedSupportLT w (Finsupp.weight w α) := by
  classical
  have hX (i : σ) : polynomialTranslate h (X i) ∈ weightedSupportLE w (w i) ∧
      polynomialTranslate h (X i) - X i ∈ weightedSupportLT w (w i) := by
    have hi : (X i : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
      simpa only [X, Finsupp.weight_single, one_smul] using weightedSupportLE_monomial w (Finsupp.single i 1) (1 : R)
    have hc : (C (h i) : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
      exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simp))
    refine ⟨by rw [polynomialTranslate_X]; exact (weightedSupportLE w _).add_mem hi hc, ?_⟩
    rw [polynomialTranslate_X, add_sub_cancel_left]
    exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simpa using hw i))
  have hsingle (i : σ) (n : ℕ) :
      polynomialTranslate h (monomial (Finsupp.single i n) 1) ∈ weightedSupportLE w (n * w i) ∧
      polynomialTranslate h (monomial (Finsupp.single i n) 1) - monomial (Finsupp.single i n) 1 ∈
        weightedSupportLT w (n * w i) := by
    induction n with
    | zero =>
      rw [Finsupp.single_zero, zero_mul]
      change polynomialTranslate h 1 ∈ weightedSupportLE w 0 ∧
        polynomialTranslate h 1 - 1 ∈ weightedSupportLT w 0
      rw [map_one, sub_self]
      exact ⟨by simpa using weightedSupportLE_monomial w (0 : σ →₀ ℕ) (1 : R), Submodule.zero_mem _⟩
    | succ n ih =>
      have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
      simp only [Finsupp.weight_single, smul_eq_mul] at hp
      have hh := translation_bounds_mul h w (monomial (Finsupp.single i n) 1) (X i)
        (n * w i) (w i) hp ih.1 (hX i).1 ih.2 (hX i).2
      simpa only [X, MvPolynomial.monomial_mul, one_mul, ← Finsupp.single_add, Nat.succ_mul] using hh
  induction α using Finsupp.induction with
  | zero =>
    change polynomialTranslate h 1 ∈ weightedSupportLE w 0 ∧
      polynomialTranslate h 1 - 1 ∈ weightedSupportLT w 0
    rw [map_one, sub_self]
    exact ⟨by simpa using weightedSupportLE_monomial w (0 : σ →₀ ℕ) (1 : R), Submodule.zero_mem _⟩
  | @single_add i n α hi hn ih =>
    have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
    have hh := translation_bounds_mul h w (monomial (Finsupp.single i n) 1) (monomial α 1)
      (Finsupp.weight w (Finsupp.single i n)) (Finsupp.weight w α) hp
      (by simpa only [Finsupp.weight_single, smul_eq_mul] using (hsingle i n).1) ih.1
      (by simpa only [Finsupp.weight_single, smul_eq_mul] using (hsingle i n).2) ih.2
    simpa only [MvPolynomial.monomial_mul, one_mul, map_add] using hh

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem mem_weightedSupportLE_iff (w : σ → ℕ) (d : ℕ) (p : MvPolynomial σ R) :
    p ∈ weightedSupportLE w d ↔ p.weightedTotalDegree w ≤ d := by
  classical
  change (∀ α ∈ p.support, Finsupp.weight w α ≤ d) ↔ _
  simp only [weightedTotalDegree, Finset.sup_le_iff]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def ofCoordinates (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) : PolynomialSlots σ d w where
  center i := aeval (fun a => X (Sum.inl a)) (P i)
  degree i := weightedSupportLE_aeval (fun _ : σ => 1) (patchVariableWeight w i)
    (fun a => X (Sum.inl a)) (fun a => weightedSupportLE_X _ (Sum.inl a)) (hP i)

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def ofCoordinates (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) (Φ : PatchKernel d) :
    PolynomialPatch σ s d where
  weight := w
  weight_pos := hw
  weight_le := hws
  weight_mono := hmono
  form := PolynomialSlots.ofCoordinates P hP
  kernel := Φ

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteProbabilityWeights Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def eventProbability {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) : ℝ := by
  classical
  exact p.mean (fun x => if E x then 1 else 0)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalRowReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rationalHeightLE_zero {H : ℕ} (hH : 1 ≤ H) : RationalHeightLE 0 H := by
  exact ⟨by simp, by simpa using hH⟩

theorem rationalHeightLE_one {H : ℕ} (hH : 1 ≤ H) : RationalHeightLE 1 H := by
  exact ⟨by simpa using hH, by simpa using hH⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem RationalHeightLE.neg {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) :
    RationalHeightLE (-q) H := by
  simpa only [RationalHeightLE, Rat.neg_num, Rat.neg_den, Int.natAbs_neg] using hq

theorem RationalHeightLE.mul {q r : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hr : RationalHeightLE r K) :
    RationalHeightLE (q * r) (H * K) := by
  have hd : (q.den : ℤ) * r.den ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast q.den_ne_zero) (by exact_mod_cast r.den_ne_zero)
  have heq : q * r = ((q.num * r.num : ℤ) : ℚ) / ((q.den : ℤ) * r.den : ℤ) := by
    push_cast
    rw [mul_div_mul_comm, Rat.num_div_den, Rat.num_div_den]
  rw [heq]
  apply rationalHeightLE_fraction _ _ hd
  · simpa only [Int.natAbs_mul] using Nat.mul_le_mul hq.1 hr.1
  · simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul hq.2 hr.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*}

theorem IntegralVector.nat_smul {x : ι → ℚ} (hx : IntegralVector x) (n : ℕ) :
    IntegralVector ((n : ℚ) • x) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => (n : ℤ) * z i, fun i => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hz, Int.cast_mul, Int.cast_natCast]

end Erdos3

end

section

namespace Erdos3

theorem denominatorGrid_subset_of_dvd {ι : Type*} {l m : ℕ} (h : l ∣ m) :
    (denominatorGrid l : Set (ι → ℚ)) ⊆ denominatorGrid m := by
  obtain ⟨k, rfl⟩ := h
  intro x hx
  have hmul := IntegralVector.nat_smul hx k
  change IntegralVector (((l * k : ℕ) : ℚ) • x)
  simpa only [smul_smul, Nat.cast_mul, mul_comm] using hmul

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealGridSeparation
namespace OAI

section

namespace Erdos3

theorem eq_zero_of_mem_realDenominatorGrid_of_abs_lt {ι : Type*} {l : ℕ}
    (hl : 0 < l) {v : ι → ℝ} (hv : v ∈ realDenominatorGrid l)
    (hsmall : ∀ i, |v i| < 1 / (l : ℝ)) : v = 0 := by
  obtain ⟨z, hz⟩ := hv
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  funext i
  have hzi : (z i : ℝ) = (l : ℝ) * v i := congrFun hz i
  have habs : |(z i : ℝ)| < 1 := by
    rw [hzi, abs_mul, abs_of_pos hl']
    simpa only [mul_comm] using (lt_div_iff₀ hl').mp (hsmall i)
  have hz0 : z i = 0 := by
    have h : |z i| < (1 : ℤ) := by exact_mod_cast habs
    have := abs_lt.mp h
    omega
  have hv0 : (l : ℝ) * v i = 0 := by simpa only [hz0, Int.cast_zero] using hzi.symm
  exact (mul_eq_zero.mp hv0).resolve_left hl'.ne'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalMatrixSeparation
namespace OAI

section

namespace Erdos3

theorem RationalHeightLE.abs_real_le {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) :
    |(q : ℝ)| ≤ H :=
  (rational_abs_real_le_numerator q).trans (Nat.cast_le.mpr hq.1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialIntegerInputs
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace RationalPolynomialHeightLE

variable {σ : Type*} {p : MvPolynomial σ ℚ} {H K : ℕ}

theorem mono (hp : RationalPolynomialHeightLE p H) (hHK : H ≤ K) :
    RationalPolynomialHeightLE p K := fun m => (hp m).mono hHK

theorem one_le (hp : RationalPolynomialHeightLE p H) : 1 ≤ H :=
  (Nat.one_le_iff_ne_zero.mpr (p.coeff 0).den_ne_zero).trans (hp 0).2

theorem C {q : ℚ} (hq : RationalHeightLE q H) :
    RationalPolynomialHeightLE (MvPolynomial.C q : MvPolynomial σ ℚ) H := by
  classical
  intro m
  rw [coeff_C]
  split_ifs
  · exact hq
  · exact rationalHeightLE_zero
      ((Nat.one_le_iff_ne_zero.mpr q.den_ne_zero).trans hq.2)

theorem X (x : σ) : RationalPolynomialHeightLE (MvPolynomial.X x : MvPolynomial σ ℚ) 1 := by
  classical
  intro m
  rw [coeff_X]
  split_ifs
  · exact rationalHeightLE_one le_rfl
  · exact rationalHeightLE_zero le_rfl

theorem C_mul {q : ℚ} (hq : RationalHeightLE q H)
    (hp : RationalPolynomialHeightLE p K) :
    RationalPolynomialHeightLE (MvPolynomial.C q * p) (H * K) := by
  intro m
  rw [coeff_C_mul]
  exact hq.mul (hp m)

theorem mul_X (hp : RationalPolynomialHeightLE p H) (x : σ) :
    RationalPolynomialHeightLE (p * MvPolynomial.X x) H := by
  classical
  intro m
  rw [coeff_mul_X']
  split_ifs
  · exact hp _
  · exact rationalHeightLE_zero hp.one_le

theorem sum_finset {ι : Type*} (t : Finset ι) (p : ι → MvPolynomial σ ℚ)
    (hp : ∀ i ∈ t, RationalPolynomialHeightLE (p i) H) :
    RationalPolynomialHeightLE (∑ i ∈ t, p i) ((t.card + 1) * H ^ t.card) := by
  classical
  simpa only [Fintype.card_coe, Finset.sum_coe_sort] using
    sum (fun i : t => p i) (fun i => hp i i.property)

end RationalPolynomialHeightLE

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LieCoordinatePolynomials
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {ι X L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def coordinateRightBracket (c : ι → ι → ι → ℚ) (x : X)
    (p : ι → MvPolynomial (X × ι) ℚ) (k : ι) : MvPolynomial (X × ι) ℚ :=
  ∑ ij : ι × ι, C (c ij.1 ij.2 k) * p ij.1 * MvPolynomial.X (x, ij.2)

noncomputable def coordinateBracketList (c : ι → ι → ι → ℚ) :
    List X → (ι → MvPolynomial (X × ι) ℚ) → (ι → MvPolynomial (X × ι) ℚ)
  | [], p => p
  | x :: xs, p => coordinateBracketList c xs (coordinateRightBracket c x p)

noncomputable def dynkinCoordinatePolynomial (c : ι → ι → ι → ℚ)
    (w : FreeSemigroup X) : ι → MvPolynomial (X × ι) ℚ :=
  coordinateBracketList c w.tail (fun i => MvPolynomial.X (w.head, i))

theorem coordinateRightBracket_totalDegree (c : ι → ι → ι → ℚ) (x : X)
    (p : ι → MvPolynomial (X × ι) ℚ) {n : ℕ}
    (hp : ∀ i, (p i).totalDegree ≤ n) (k : ι) :
    (coordinateRightBracket c x p k).totalDegree ≤ n + 1 := by
  apply totalDegree_finsetSum_le
  intro ij _
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_X]
    have h := totalDegree_mul (C (c ij.1 ij.2 k)) (p ij.1)
    rw [totalDegree_C, zero_add] at h
    exact Nat.add_le_add_right (h.trans (hp ij.1)) 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateHeight
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {ι X : Type*} [Fintype ι]

theorem coordinateRightBracket_height (c : ι → ι → ι → ℚ) {H K : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (x : X)
    (p : ι → MvPolynomial (X × ι) ℚ)
    (hp : ∀ i, RationalPolynomialHeightLE (p i) K) (k : ι) :
    RationalPolynomialHeightLE (coordinateRightBracket c x p k)
      ((Fintype.card ι ^ 2 + 1) * (H * K) ^ (Fintype.card ι ^ 2)) := by
  have h := RationalPolynomialHeightLE.sum
    (fun ij : ι × ι => C (c ij.1 ij.2 k) * p ij.1 * MvPolynomial.X (x, ij.2))
    (fun ij => (RationalPolynomialHeightLE.C_mul (hc ij.1 ij.2 k) (hp ij.1)).mul_X (x, ij.2))
  simpa only [coordinateRightBracket, Fintype.card_prod, pow_two] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateScalarExtension
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {ι X R L : Type*} [Fintype ι] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]

theorem coordinateRightBracket_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (x : X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
      (coordinateRightBracket c x p k) = e.repr ⁅a, f x⁆ k := by
  simp only [coordinateRightBracket, map_sum, map_mul, aeval_C, aeval_X, hp]
  exact (lie_coordinate_formula_over e c hc a (f x) k).symm

variable [LieAlgebra ℚ L]

theorem coordinateBracketList_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (xs : List X) (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (coordinateBracketList c xs p k) = e.repr (rightBracketList f xs a) k := by
  induction xs generalizing p a with
  | nil => exact hp k
  | cons x xs ih =>
    exact ih (coordinateRightBracket c x p) ⁅a, f x⁆
      (coordinateRightBracket_eval_over e c hc f p a hp x)

theorem dynkinCoordinatePolynomial_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (w : FreeSemigroup X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (dynkinCoordinatePolynomial c w k) =
      e.repr (dynkinWord f w) k := by
  apply coordinateBracketList_eval_over e c hc
  intro i
  simp only [aeval_X]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3

namespace NilpotentAlgebraFiltration
variable {A : Type*} [Ring A] [Algebra ℚ A] {s t : ℕ}

def extend (F : NilpotentAlgebraFiltration A s) (hst : s ≤ t) : NilpotentAlgebraFiltration A t where
  layer := F.layer
  antitone := F.antitone
  zero_eq_top := F.zero_eq_top
  mul_mem := F.mul_mem
  terminal := le_antisymm (by
    rw [← F.terminal]
    exact F.antitone (Nat.add_le_add_right hst 1)) bot_le

end NilpotentAlgebraFiltration

attribute [local instance] LieRing.ofAssociativeRing

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieFiniteProduct
namespace OAI

section

namespace Erdos3

open Module

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]

variable {R : Type*} [CommRing R] [∀ a, LieAlgebra R (M a)]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

def liePiMap (φ : ∀ a, L →ₗ⁅R⁆ M a) : L →ₗ⁅R⁆ (∀ a, M a) where
  toLinearMap := LinearMap.pi (fun a => (φ a).toLinearMap)
  map_lie' {x y} := by funext a; exact (φ a).map_lie x y

@[simp] theorem liePiMap_apply (φ : ∀ a, L →ₗ⁅R⁆ M a) (x : L) (a : α) :
    liePiMap φ x a = φ a x := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def rectangularWeightIndices (a S : J → ℝ) (R : ℝ) : Finset (J → ℤ) := by
  classical
  exact Fintype.piFinset fun j => sampledWeightIndices (a j) (S j) R

theorem rectangularWeight_zero_off_indices (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0)
    (k : J → ℤ) (hk : k ∉ rectangularWeightIndices a S R) : rectangularWeight f a S k = 0 := by
  classical
  by_contra hn
  have hb : ‖rectangularLatticePoint a S k‖ ≤ R := by
    by_contra! h
    exact hn (hsupport _ h)
  apply hk
  apply Fintype.mem_piFinset.mpr
  intro j
  have hj : |((k j : ℝ) - a j) / S j| ≤ R :=
    (norm_le_pi_norm (rectangularLatticePoint a S k) j).trans hb
  obtain ⟨hlo, hhi⟩ := abs_le.mp hj
  have hlo' := (le_div_iff₀ (hS j)).mp hlo
  have hhi' := (div_le_iff₀ (hS j)).mp hhi
  apply Finset.mem_Icc.mpr
  exact ⟨Int.ceil_le.mpr (by nlinarith), Int.le_floor.mpr (by nlinarith)⟩

theorem rectangularWeight_summable (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    Summable (rectangularWeight f a S) :=
  (hasSum_sum_of_ne_finset_zero (rectangularWeight_zero_off_indices f a S hS hsupport)).summable

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealWeightPMF
namespace OAI

section

namespace Erdos3

open scoped ENNReal

theorem realWeightPMF_apply {X : Type*} (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : Summable w) (hZ : 0 < ∑' x, w x) (x : X) :
    (realWeightPMF w hw hs hZ x).toReal = w x / ∑' y, w y :=
  ENNReal.toReal_ofReal (div_nonneg (hw x) hZ.le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def smoothProductProfile (I : Type*) [Fintype I] (x : I → ℝ) : ℝ :=
  ∏ i, smoothProbabilityProfile (x i)

theorem smoothProductProfile_range (I : Type*) [Fintype I] (x : I → ℝ) :
    0 ≤ smoothProductProfile I x ∧ smoothProductProfile I x ≤ 1 :=
  ⟨Finset.prod_nonneg (fun i _ => (smoothProbabilityProfile_range (x i)).1),
    Finset.prod_le_one (fun i _ => (smoothProbabilityProfile_range (x i)).1)
      (fun i _ => (smoothProbabilityProfile_range (x i)).2)⟩

theorem smoothProductProfile_zero_outside (I : Type*) [Fintype I]
    (x : I → ℝ) (hx : 1 < ‖x‖) : smoothProductProfile I x = 0 := by
  classical
  by_contra hn
  apply (not_le_of_gt hx)
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  by_contra! hi
  exact hn (Finset.prod_eq_zero (Finset.mem_univ i)
    (smoothProbabilityProfile_zero_outside (x i) hi))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedLoweringGroup
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weightedSupportLT_le {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w d) : p ∈ weightedSupportLE w d :=
  fun _ ha => le_of_lt (show _ < d from hp ha)

theorem weightedSupportLT_succ_le {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w (d + 1)) : p ∈ weightedSupportLE w d :=
  fun _ ha => Nat.lt_succ_iff.mp (hp ha)

theorem weightedLowering_preserves_degree (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    F p ∈ weightedSupportLE w d := by
  rw [MvPolynomial.aeval_unique F]
  apply weightedSupportLE_aeval w w _ _ hp
  intro i
  simpa only [sub_add_cancel, Function.comp_apply] using (weightedSupportLE w (w i)).add_mem
    (weightedSupportLT_le (hF i)) (weightedSupportLE_X w i)

theorem weightedLowering_mul_bounds (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (p q : MvPolynomial σ R) (d e : ℕ)
    (hp : p ∈ weightedSupportLE w d)
    (hFp : F p ∈ weightedSupportLE w d) (hFq : F q ∈ weightedSupportLE w e)
    (hdp : F p - p ∈ weightedSupportLT w d)
    (hdq : F q - q ∈ weightedSupportLT w e) :
    F (p * q) ∈ weightedSupportLE w (d + e) ∧
      F (p * q) - p * q ∈ weightedSupportLT w (d + e) := by
  refine ⟨by rw [map_mul]; exact weightedSupportLE_mul hFp hFq, ?_⟩
  rw [map_mul, show F p * F q - p * q = (F p - p) * F q + p * (F q - q) by ring]
  exact (weightedSupportLT w (d + e)).add_mem (weightedSupportLT_mul_LE hdp hFq)
    (weightedSupportLE_mul_LT hp hdq)

theorem weightedLowering_monomial_one (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) (a : σ →₀ ℕ) :
    F (monomial a 1) - monomial a 1 ∈ weightedSupportLT w (Finsupp.weight w a) := by
  classical
  have hsingle (i : σ) (n : ℕ) :
      F (monomial (Finsupp.single i n) 1) - monomial (Finsupp.single i n) 1 ∈
        weightedSupportLT w (n * w i) := by
    induction n with
    | zero =>
        simp only [Finsupp.single_zero, zero_mul]
        change F 1 - 1 ∈ _
        rw [map_one, sub_self]
        exact Submodule.zero_mem _
    | succ n ih =>
        have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
        simp only [Finsupp.weight_single, smul_eq_mul] at hp
        have hh := weightedLowering_mul_bounds w F (monomial (Finsupp.single i n) 1)
          (X i) (n * w i) (w i) hp (weightedLowering_preserves_degree w F hF hp)
          (weightedLowering_preserves_degree w F hF (weightedSupportLE_X w i)) ih (hF i)
        simpa only [X, MvPolynomial.monomial_mul, one_mul, ← Finsupp.single_add, Nat.succ_mul]
          using hh.2
  induction a using Finsupp.induction with
  | zero =>
      change F 1 - 1 ∈ weightedSupportLT w 0
      rw [map_one, sub_self]
      exact Submodule.zero_mem _
  | @single_add i n a hi hn ih =>
      have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
      have hq := weightedSupportLE_monomial w a (1 : R)
      have hh := weightedLowering_mul_bounds w F (monomial (Finsupp.single i n) 1)
        (monomial a 1) (Finsupp.weight w (Finsupp.single i n)) (Finsupp.weight w a)
        hp (weightedLowering_preserves_degree w F hF hp)
        (weightedLowering_preserves_degree w F hF hq)
        (by simpa only [Finsupp.weight_single, smul_eq_mul] using hsingle i n) ih
      simpa only [MvPolynomial.monomial_mul, one_mul, map_add] using hh.2

theorem weightedLowering_monomial (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) (a : σ →₀ ℕ) (r : R) :
    F (monomial a r) - monomial a r ∈ weightedSupportLT w (Finsupp.weight w a) := by
  have hc : F (C r) = C r := F.commutes r
  have hm : C r * monomial a (1 : R) = monomial a r := by
    change monomial 0 r * monomial a 1 = monomial a r
    rw [MvPolynomial.monomial_mul, zero_add, mul_one]
  rw [← hm, map_mul, hc, ← mul_sub]
  simpa only [zero_add] using weightedSupportLE_mul_LT (weightedSupportLE_C w 0 r)
    (weightedLowering_monomial_one w F hF a)

theorem weightedLowering_difference (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    F p - p ∈ weightedSupportLT w d := by
  classical
  change (F.toLinearMap - (LinearMap.id : Module.End R (MvPolynomial σ R))) p ∈
    weightedSupportLT w d
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLT w d).sum_mem
  intro a ha
  exact weightedSupportLT_mono (hp ha) (weightedLowering_monomial w F hF a (p.coeff a))

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem polynomialHomDifference_pow_eq_zero (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    (polynomialHomDifference F ^ (d + 1)) p = 0 := by
  induction d generalizing p with
  | zero =>
      rw [pow_one]
      exact weightedSupportLT_zero_eq (weightedLowering_difference w F hF hp)
  | succ d ih =>
      rw [pow_succ, Module.End.mul_apply]
      exact ih (weightedSupportLT_succ_le (weightedLowering_difference w F hF hp))

theorem weightedLowering_eq_zero_of_degree (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) (hz : F p = 0) :
    p = 0 := by
  induction d generalizing p with
  | zero =>
      have h := weightedLowering_difference w F hF hp
      rw [hz, zero_sub] at h
      exact neg_eq_zero.mp (weightedSupportLT_zero_eq h)
  | succ d ih =>
      have h := weightedLowering_difference w F hF hp
      rw [hz, zero_sub] at h
      have hlow : p ∈ weightedSupportLT w (d + 1) := by
        simpa only [neg_neg] using (weightedSupportLT w (d + 1)).neg_mem h
      exact ih (weightedSupportLT_succ_le hlow) hz

theorem weightedLowering_injective (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) : Function.Injective F := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply weightedLowering_eq_zero_of_degree w F hF
    ((mem_weightedSupportLE_iff w ((p - q).weightedTotalDegree w) (p - q)).mpr le_rfl)
  rw [map_sub, hpq, sub_self]

theorem weightedLowering_preimage_degree (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    ∃ q, q ∈ weightedSupportLE w d ∧ F q = p := by
  induction d generalizing p with
  | zero =>
      exact ⟨p, hp, sub_eq_zero.mp (weightedSupportLT_zero_eq
        (weightedLowering_difference w F hF hp))⟩
  | succ d ih =>
      have hdiff := weightedSupportLT_succ_le (weightedLowering_difference w F hF hp)
      obtain ⟨q, hq, heq⟩ := ih hdiff
      refine ⟨p - q, (weightedSupportLE w (d + 1)).sub_mem hp
        (weightedSupportLE_mono (Nat.le_succ d) hq), ?_⟩
      rw [map_sub, heq]
      abel

theorem weightedLowering_bijective (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) : Function.Bijective F := by
  refine ⟨weightedLowering_injective w F hF, ?_⟩
  intro p
  obtain ⟨q, _, hq⟩ := weightedLowering_preimage_degree w F hF
    ((mem_weightedSupportLE_iff w (p.weightedTotalDegree w) p).mpr le_rfl)
  exact ⟨q, hq⟩

noncomputable def weightedLoweringEquiv (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofBijective F (weightedLowering_bijective w F hF)

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

def weightedLoweringSubgroup (w : σ → ℕ) :
    Subgroup (MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) where
  carrier := {e | ∀ i, e (X i) - X i ∈ weightedSupportLT w (w i)}
  one_mem' := by
    intro i
    change X i - X i ∈ weightedSupportLT w (w i)
    rw [sub_self]
    exact Submodule.zero_mem _
  mul_mem' := by
    intro e f he hf i
    have hp := weightedLowering_preserves_degree w f.toAlgHom hf (weightedSupportLE_X w i)
    have h := weightedLowering_difference w e.toAlgHom he hp
    change e (f (X i)) - f (X i) ∈ weightedSupportLT w (w i) at h
    change e (f (X i)) - X i ∈ weightedSupportLT w (w i)
    simpa only [sub_add_sub_cancel] using (weightedSupportLT w (w i)).add_mem h (hf i)
  inv_mem' := by
    intro e he i
    obtain ⟨q, hq, hqe⟩ := weightedLowering_preimage_degree w e.toAlgHom he
      (weightedSupportLE_X w i)
    change e q = X i at hqe
    have heq : e.symm (X i) = q := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hqe.symm
    change e.symm (X i) - X i ∈ weightedSupportLT w (w i)
    rw [heq]
    have h := weightedLowering_difference w e.toAlgHom he hq
    change e q - q ∈ weightedSupportLT w (w i) at h
    rw [hqe] at h
    simpa only [neg_sub] using (weightedSupportLT w (w i)).neg_mem h

abbrev WeightedLoweringAut (w : σ → ℕ) (R : Type*) [CommRing R] :=
  ↥(weightedLoweringSubgroup (R := R) w)

theorem weightedLoweringEquiv_mem (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) :
    weightedLoweringEquiv w F hF ∈ weightedLoweringSubgroup w := hF

noncomputable def WeightedLoweringAut.ofHom (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) : WeightedLoweringAut w R :=
  ⟨weightedLoweringEquiv w F hF, weightedLoweringEquiv_mem w F hF⟩

theorem WeightedLoweringAut.preserves_degree {w : σ → ℕ} (e : WeightedLoweringAut w R)
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    e.val p ∈ weightedSupportLE w d :=
  weightedLowering_preserves_degree w e.val.toAlgHom e.property hp

theorem WeightedLoweringAut.difference_lower {w : σ → ℕ} (e : WeightedLoweringAut w R)
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    e.val p - p ∈ weightedSupportLT w d :=
  weightedLowering_difference w e.val.toAlgHom e.property hp

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedSupportDropRename
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weightedSupportDrop_zero (w : σ → ℕ) (n : ℕ) :
    weightedSupportDrop (R := R) w n 0 = weightedSupportLE w n := by
  ext P
  simp only [mem_weightedSupportDrop_iff, Nat.add_zero]
  rfl

theorem weightedSupportDrop_one (w : σ → ℕ) (n : ℕ) :
    weightedSupportDrop (R := R) w n 1 = weightedSupportLT w n := by
  ext P
  simp only [mem_weightedSupportDrop_iff, Nat.add_one_le_iff]
  rfl

theorem weightedSupportDrop_le {w : σ → ℕ} {n r : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportDrop w n r) : P ∈ weightedSupportLE w n := by
  rw [← weightedSupportDrop_zero]
  exact weightedSupportDrop_antitone (Nat.zero_le _) hP

theorem weightedSupportDrop_mul_LE {w : σ → ℕ} {d e r : ℕ} {P Q : MvPolynomial σ R}
    (hP : P ∈ weightedSupportDrop w d r) (hQ : Q ∈ weightedSupportLE w e) :
    P * Q ∈ weightedSupportDrop w (d + e) r := by
  rw [← weightedSupportDrop_zero] at hQ
  simpa only [Nat.add_zero] using weightedSupportDrop_mul hP hQ

theorem weightedSupportLE_mul_drop {w : σ → ℕ} {d e r : ℕ} {P Q : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLE w d) (hQ : Q ∈ weightedSupportDrop w e r) :
    P * Q ∈ weightedSupportDrop w (d + e) r := by
  rw [mul_comm, Nat.add_comm d e]
  exact weightedSupportDrop_mul_LE hQ hP

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedDerivationDrop
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weightedDerivation_mul (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (P Q : MvPolynomial σ R) (d e k : ℕ)
    (hP : P ∈ weightedSupportLE w d) (hQ : Q ∈ weightedSupportLE w e)
    (hDP : D P ∈ weightedSupportDrop w d k) (hDQ : D Q ∈ weightedSupportDrop w e k) :
    D (P * Q) ∈ weightedSupportDrop w (d + e) k := by
  rw [D.leibniz, smul_eq_mul, smul_eq_mul]
  apply (weightedSupportDrop w (d + e) k).add_mem (weightedSupportLE_mul_drop hP hDQ)
  simpa only [Nat.add_comm e d] using weightedSupportLE_mul_drop hQ hDP

theorem weightedDerivation_monomial_one (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k) (a : σ →₀ ℕ) :
    D (monomial a 1) ∈ weightedSupportDrop w (Finsupp.weight w a) k := by
  classical
  have hsingle (i : σ) (n : ℕ) :
      D (monomial (Finsupp.single i n) 1) ∈ weightedSupportDrop w (n * w i) k := by
    induction n with
    | zero =>
        simp only [Finsupp.single_zero, zero_mul]
        change D 1 ∈ _
        rw [D.map_one_eq_zero]
        exact Submodule.zero_mem _
    | succ n ih =>
        have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
        simp only [Finsupp.weight_single, smul_eq_mul] at hp
        have hh := weightedDerivation_mul w D (monomial (Finsupp.single i n) 1)
          (X i) (n * w i) (w i) k hp (weightedSupportLE_X w i) ih (hD i)
        simpa only [X, MvPolynomial.monomial_mul, one_mul, ← Finsupp.single_add, Nat.succ_mul]
          using hh
  induction a using Finsupp.induction with
  | zero =>
      change D 1 ∈ weightedSupportDrop w 0 k
      rw [D.map_one_eq_zero]
      exact Submodule.zero_mem _
  | @single_add i n a hi hn ih =>
      have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
      have hq := weightedSupportLE_monomial w a (1 : R)
      have hh := weightedDerivation_mul w D (monomial (Finsupp.single i n) 1)
        (monomial a 1) (Finsupp.weight w (Finsupp.single i n)) (Finsupp.weight w a) k hp hq
        (by simpa only [Finsupp.weight_single, smul_eq_mul] using hsingle i n) ih
      simpa only [MvPolynomial.monomial_mul, one_mul, map_add] using hh

theorem weightedDerivation_monomial (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k) (a : σ →₀ ℕ) (c : R) :
    D (monomial a c) ∈ weightedSupportDrop w (Finsupp.weight w a) k := by
  have hm : C c * monomial a (1 : R) = monomial a c := by
    change monomial 0 c * monomial a 1 = monomial a c
    rw [MvPolynomial.monomial_mul, zero_add, mul_one]
  rw [← hm, D.leibniz, MvPolynomial.derivation_C, smul_zero, add_zero, smul_eq_mul]
  simpa only [zero_add] using weightedSupportLE_mul_drop (weightedSupportLE_C w 0 c)
    (weightedDerivation_monomial_one w D k hD a)

theorem weightedDerivation_apply (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k)
    {n r : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportDrop w n r) :
    D P ∈ weightedSupportDrop w n (r + k) := by
  classical
  rw [← P.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportDrop w n (r + k)).sum_mem
  intro a ha
  have hm := weightedDerivation_monomial w D k hD a (P.coeff a)
  intro b hb
  have h1 : Finsupp.weight w b + k ≤ Finsupp.weight w a := hm hb
  have h2 : Finsupp.weight w a + r ≤ n := hP ha
  change Finsupp.weight w b + (r + k) ≤ n
  omega

theorem weightedDerivation_apply_le (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k)
    {n : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportLE w n) :
    D P ∈ weightedSupportDrop w n k := by
  rw [← weightedSupportDrop_zero] at hP
  simpa only [Nat.zero_add] using weightedDerivation_apply w D k hD hP

theorem weightedDerivation_bracket (w : σ → ℕ)
    (D E : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (a b : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) a)
    (hE : ∀ i, E (X i) ∈ weightedSupportDrop w (w i) b) (i : σ) :
    ⁅D, E⁆ (X i) ∈ weightedSupportDrop w (w i) (a + b) := by
  rw [Derivation.commutator_apply]
  apply (weightedSupportDrop w (w i) (a + b)).sub_mem
  · simpa only [Nat.add_comm b a] using weightedDerivation_apply w D a hD (hE i)
  · exact weightedDerivation_apply w E b hE (hD i)

theorem weightedDerivation_pow (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k)
    {n r : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportDrop w n r) (m : ℕ) :
    (D.toLinearMap ^ m) P ∈ weightedSupportDrop w n (r + m * k) := by
  induction m with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.zero_mul, Nat.add_zero] using hP
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      change D ((D.toLinearMap ^ m) P) ∈ weightedSupportDrop w n (r + (m + 1) * k)
      simpa only [Nat.succ_mul, Nat.add_assoc] using weightedDerivation_apply w D k hD ih

theorem weightedDerivation_pow_eq_zero (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) 1)
    {n : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportLE w n) :
    (D.toLinearMap ^ (n + 1)) P = 0 := by
  rw [← weightedSupportDrop_zero] at hP
  have h := weightedDerivation_pow w D 1 hD hP (n + 1)
  simp only [Nat.mul_one, Nat.zero_add] at h
  exact weightedSupportDrop_eq_zero (Nat.lt_succ_self n) h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateSmooth
namespace OAI

section

namespace Erdos3

open Module
open scoped ContDiff

variable {ι X E L : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LieRing L] [LieAlgebra ℝ L] {n : ℕ∞ω}

variable [LieAlgebra ℚ L]

theorem contDiff_rightBracketList_coordinates (e : Basis ι ℝ L) (f : X → E → L)
    (hf : ∀ x i, ContDiff ℝ n (fun y => e.repr (f x y) i)) (xs : List X)
    (a : E → L) (ha : ∀ i, ContDiff ℝ n (fun y => e.repr (a y) i)) (k : ι) :
    ContDiff ℝ n (fun y => e.repr (rightBracketList (fun x => f x y) xs (a y)) k) := by
  induction xs generalizing a with
  | nil => exact ha k
  | cons x xs ih =>
    exact ih (fun y => ⁅a y, f x y⁆) (contDiff_lie_coordinates e a (f x) ha (hf x))

theorem contDiff_dynkinWord_coordinates (e : Basis ι ℝ L) (f : X → E → L)
    (hf : ∀ x i, ContDiff ℝ n (fun y => e.repr (f x y) i))
    (w : FreeSemigroup X) (k : ι) :
    ContDiff ℝ n (fun y => e.repr (dynkinWord (fun x => f x y) w) k) :=
  contDiff_rightBracketList_coordinates e f hf w.tail (f w.head) (hf w.head) k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def cyclicIntegerCharacter (M : ℕ) [NeZero M] (z : ℤ) : AddChar (ZMod M) ℂ where
  toFun r := character (ZMod.toAddCircle (r * (z : ZMod M)))
  map_zero_eq_one' := by simp only [zero_mul, map_zero, character_zero]
  map_add_eq_mul' r s := by
    simp only [add_mul, map_add, character_add]

noncomputable def integerGridCharacter (M : ℕ) [NeZero M] (k : Fin M) (z : ℤ) : ℂ :=
  cyclicIntegerCharacter M z (gridResidueEquiv M k)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def rectangularGridCharacter {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) : ℂ :=
  ∏ j, integerGridCharacter M (k j) (y j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteImageMass {X H : Type*} [Fintype X] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) : ℝ :=
  p.mean (fun x => if Y x = z then 1 else 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {X : Type*} (N H : X → ℕ) (lo a : X → ℤ) (M : ℕ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))

include hM hbox hne in
theorem physicalResidue_start_nonneg (i : X) :
    0 ≤ a i + M * residueIndexLower (lo i) M (a i) := by
  have hx := (physicalResidueCoordinateEquiv (lo i) (lo i + H i) (a i) M hM
    ⟨0, hne i⟩).property
  have hlow := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).1
  rw [physicalResidueCoordinateEquiv_val] at hlow
  have hboxlow := (hbox i).1
  simpa only [Nat.cast_zero, add_zero] using hboxlow.trans hlow

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {σ R V : Type*} [Fintype σ]
  [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_linearPolynomial_single (a : σ → V) (i : σ) :
    coefficients (linearPolynomial (R := R) a) (Finsupp.single i 1) = a i := by
  rw [linearPolynomial_apply, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · rw [coefficients_monomial, Finsupp.single_eq_same]
  · intro j _ hji
    rw [coefficients_monomial, Finsupp.single_eq_of_ne]
    exact fun h => hji ((Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)) h.symm)
  · simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def outsideDownsetIdeal (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) :
    LieIdeal R (VectorPolynomial σ R L) :=
  { coefficientSupport Jᶜ with
    lie_mem := by
      classical
      intro p q hq
      change ∀ a, a ∉ Jᶜ → coefficients q a = 0 at hq
      have hq' : ∀ a ∈ J, coefficients q a = 0 := by
        simpa only [Set.mem_compl_iff, not_not] using hq
      rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
      simp only [Finsupp.sum]
      rw [sum_lie_sum]
      apply (coefficientSupport Jᶜ).sum_mem
      intro a _
      apply (coefficientSupport Jᶜ).sum_mem
      intro b hb
      rw [lie_monomial]
      apply monomial_mem_coefficientSupport
      intro hab
      have hle : b ≤ a + b := by
        intro i
        simp only [Finsupp.add_apply]
        omega
      exact (Finsupp.mem_support_iff.mp hb) (hq' b (hJ hle hab)) }

@[simp] theorem mem_outsideDownsetIdeal (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)
    (p : VectorPolynomial σ R L) :
    p ∈ outsideDownsetIdeal (R := R) (L := L) J hJ ↔ ∀ a ∈ J, coefficients p a = 0 := by
  change (∀ a, a ∉ Jᶜ → coefficients p a = 0) ↔ _
  simp only [Set.mem_compl_iff, not_not]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R S L : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [LieRing L] [LieAlgebra R L] [LieAlgebra S L] [IsScalarTower R S L]

noncomputable def eval₂Lie (x : σ → S) : VectorPolynomial σ R L →ₗ⁅R⁆ L where
  toLinearMap := eval₂ x
  map_lie' {p q} := by
    change eval₂ x ⁅p, q⁆ = ⁅eval₂ x p, eval₂ x q⁆
    induction p using TensorProduct.induction_on with
    | zero =>
      exact (congrArg _ (zero_lie (M := VectorPolynomial σ R L) q)).trans (by rw [map_zero, zero_lie])
    | tmul a v =>
      induction q using TensorProduct.induction_on with
      | zero =>
        exact (congrArg _ (lie_zero (L := VectorPolynomial σ R L) (a ⊗ₜ[R] v))).trans (by rw [map_zero, lie_zero])
      | tmul b w =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, eval₂_tmul, map_mul,
          smul_lie, lie_smul, smul_smul, mul_comm]
      | add p q hp hq => rw [LieRing.lie_add, map_add, hp, hq, map_add, LieRing.lie_add]
    | add p q hp hq => rw [LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]

@[simp] theorem eval₂Lie_apply (x : σ → S) (p : VectorPolynomial σ R L) :
    eval₂Lie (R := R) (L := L) x p = eval₂ x p := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module

section Lie

variable {σ K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

noncomputable def coefficientSubmodule (U : Submodule K L) : Submodule K (VectorPolynomial σ K L) where
  carrier := {p | ∀ α, coefficients p α ∈ U}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using U.add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using U.smul_mem c (hp α)

theorem monomial_mem_coefficientSubmodule (U : Submodule K L) (α : σ →₀ ℕ) {v : L} (hv : v ∈ U) :
    monomial (R := K) α v ∈ coefficientSubmodule U := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hv
  · simp [h]

noncomputable def coefficientLieSubalgebra (U : LieSubalgebra K L) :
    LieSubalgebra K (VectorPolynomial σ K L) :=
  { coefficientSubmodule U.toSubmodule with
    lie_mem' := by
      intro p q hp hq
      classical
      rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
      simp only [Finsupp.sum]
      rw [sum_lie_sum (coefficients p).support (coefficients q).support
        (fun α => monomial (R := K) α (coefficients p α))
        (fun β => monomial (R := K) β (coefficients q β))]
      apply Submodule.sum_mem
      intro α _
      apply Submodule.sum_mem
      intro β _
      rw [lie_monomial]
      exact monomial_mem_coefficientSubmodule U.toSubmodule _ (U.lie_mem (hp α) (hq β)) }

end Lie

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open VectorPolynomial

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficient_zero_of_squarefreeKernel (p : VectorPolynomial ι ℚ L)
    (hp : p ∈ LinearMap.ker squarefreeCoefficients) (a : ι →₀ ℕ) (ha : SquarefreeExponent a) :
    coefficients p a = 0 :=
  congrFun (LinearMap.mem_ker.mp hp) ⟨a, ha⟩

theorem squarefreeKernel_lie_mem (p q : VectorPolynomial ι ℚ L)
    (hq : q ∈ LinearMap.ker squarefreeCoefficients) :
    ⁅p, q⁆ ∈ LinearMap.ker squarefreeCoefficients := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun a => monomial (R := ℚ) a (coefficients p a))
    (fun b => monomial (R := ℚ) b (coefficients q b))]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  rw [lie_monomial]
  by_cases hb : SquarefreeExponent b
  · rw [coefficient_zero_of_squarefreeKernel q hq b hb, lie_zero]
    simpa only [monomial, TensorProduct.tmul_zero] using
      (LinearMap.ker (squarefreeCoefficients (ι := ι) (L := L))).zero_mem
  · exact monomial_mem_squarefreeKernel (a + b) (not_squarefreeExponent_add_right a b hb) _

noncomputable def squarefreePolynomialIdeal : LieIdeal ℚ (VectorPolynomial ι ℚ L) :=
  { LinearMap.ker squarefreeCoefficients with
    lie_mem := fun {p q} hq => squarefreeKernel_lie_mem p q hq }

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedSmoothProductLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def shiftedSmoothProductMass {I : Type*} [Fintype I]
    (a S : I → ℝ) : ℝ := ∑' x, rectangularWeight (smoothProductProfile I) a S x

noncomputable def shiftedSmoothProductPMF {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) : PMF (I → ℤ) :=
  realWeightPMF (rectangularWeight (smoothProductProfile I) a S)
    (fun _ => (smoothProductProfile_range I _).1)
    (rectangularWeight_summable _ a S hS (smoothProductProfile_zero_outside I)) hZ

theorem shiftedSmoothProductPMF_toReal {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) (x : I → ℤ) :
    (shiftedSmoothProductPMF a S hS hZ x).toReal =
      rectangularWeight (smoothProductProfile I) a S x / shiftedSmoothProductMass a S :=
  realWeightPMF_apply _ _ _ _ x

theorem shiftedSmoothProductPMF_toReal_zero_off {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (x : I → ℤ) (hx : x ∉ rectangularWeightIndices a S 1) :
    (shiftedSmoothProductPMF a S hS hZ x).toReal = 0 := by
  rw [shiftedSmoothProductPMF_toReal,
    rectangularWeight_zero_off_indices _ a S hS (smoothProductProfile_zero_outside I) x hx,
    zero_div]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

namespace PolynomialTranslationGroup

noncomputable instance instMul : Mul (PolynomialTranslationGroup σ) where
  mul a b := ⟨a.base + b.base, polynomialTranslate (-b.base) a.polynomial + b.polynomial⟩

noncomputable instance instInv : Inv (PolynomialTranslationGroup σ) where
  inv a := ⟨-a.base, -polynomialTranslate a.base a.polynomial⟩

@[simp] theorem base_mul (a b : PolynomialTranslationGroup σ) :
    (a * b).base = a.base + b.base := rfl

@[simp] theorem polynomial_mul (a b : PolynomialTranslationGroup σ) :
    (a * b).polynomial = polynomialTranslate (-b.base) a.polynomial + b.polynomial := rfl

@[simp] theorem base_one : (1 : PolynomialTranslationGroup σ).base = 0 := rfl
@[simp] theorem polynomial_one : (1 : PolynomialTranslationGroup σ).polynomial = 0 := rfl
@[simp] theorem base_inv (a : PolynomialTranslationGroup σ) : (a⁻¹).base = -a.base := rfl
@[simp] theorem polynomial_inv (a : PolynomialTranslationGroup σ) :
    (a⁻¹).polynomial = -polynomialTranslate a.base a.polynomial := rfl

end PolynomialTranslationGroup
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationGroup

open _root_.MvPolynomial
variable {σ : Type*}

noncomputable def actionHom (g : PolynomialTranslationGroup σ) :
    MvPolynomial (σ ⊕ Unit) ℚ →ₐ[ℚ] MvPolynomial (σ ⊕ Unit) ℚ :=
  aeval (Sum.elim (fun i => X (Sum.inl i) + C (g.base i))
    (fun u => X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial)))

@[simp] theorem actionHom_X_inl (g : PolynomialTranslationGroup σ) (i : σ) :
    actionHom g (X (Sum.inl i)) = X (Sum.inl i) + C (g.base i) := by simp [actionHom]

@[simp] theorem actionHom_X_inr (g : PolynomialTranslationGroup σ) (u : Unit) :
    actionHom g (X (Sum.inr u)) =
      X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial) := by simp [actionHom]

@[simp] theorem actionHom_C (g : PolynomialTranslationGroup σ) (r : ℚ) :
    actionHom g (C r) = C r := by simp [actionHom]

end Erdos3.PolynomialTranslationGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedSubstitutionSupport
namespace OAI

section

namespace Erdos3

theorem aeval_monomial_weightedSupport {σ τ R : Type*} [CommRing R]
    (f : σ → MvPolynomial τ R) (w : σ → ℕ) (v : τ → ℕ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) (α : σ →₀ ℕ)
    {β : τ →₀ ℕ}
    (hβ : β ∈ (MvPolynomial.aeval (R := R) f (MvPolynomial.monomial α 1)).support) :
    Finsupp.weight v β ≤ Finsupp.weight w α :=
  weightedSupportLE_aeval_monomial w v f hf α 1 hβ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorWeightedDegreeTools
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

theorem earlierSlot_ne_self (i : Fin d) (j : Fin i.val) : earlierSlot i j ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  change j.val = i.val at hv
  omega

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientNormalization
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

noncomputable def roundedIntegerPolynomial (P : MvPolynomial σ ℝ) : MvPolynomial σ ℤ :=
  .ofCoeff ((AddMonoidAlgebra.coeff P).mapRange round round_zero)

@[simp] theorem roundedIntegerPolynomial_coeff (P : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    (roundedIntegerPolynomial P).coeff a = round (P.coeff a) := rfl

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

def patchSlotWeight {d : ℕ} (w : Fin d → ℕ) (i : Fin d) : σ ⊕ Fin i.val → ℕ :=
  Sum.elim (fun _ => 0) (fun j => w (earlierSlot i j))

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] {d : ℕ}

namespace PolynomialSlots

variable {w : Fin d → ℕ}

noncomputable def specializeCenter (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    MvPolynomial (Fin i.val) ℝ := aeval (Sum.elim (fun a => C (t a)) X) (A.center i)

end PolynomialSlots

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*}

noncomputable def floorIntegerPolynomial (D : MvPolynomial σ ℝ) : MvPolynomial σ ℤ :=
  .ofCoeff ((AddMonoidAlgebra.coeff D).mapRange Int.floor Int.floor_zero)

@[simp] theorem floorIntegerPolynomial_coeff (D : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    (floorIntegerPolynomial D).coeff a = ⌊D.coeff a⌋ := rfl

noncomputable def fractionalCoefficientPolynomial (D : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  D - MvPolynomial.map (Int.castRingHom ℝ) (floorIntegerPolynomial D)

@[simp] theorem fractionalCoefficientPolynomial_coeff (D : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    (fractionalCoefficientPolynomial D).coeff a = Int.fract (D.coeff a) := by
  simp only [fractionalCoefficientPolynomial, coeff_sub, coeff_map,
    floorIntegerPolynomial_coeff, Int.fract]
  rfl

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem polynomialDerivationDrop_bracket (w : σ → ℕ) (a b : ℕ)
    {D E : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)}
    (hD : D ∈ polynomialDerivationDrop w a) (hE : E ∈ polynomialDerivationDrop w b) :
    ⁅D, E⁆ ∈ polynomialDerivationDrop w (a + b) :=
  weightedDerivation_bracket w D E a b hD hE

noncomputable def polynomialLoweringLieAlgebra (w : σ → ℕ) :
    LieSubalgebra R (Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) :=
  { polynomialDerivationDrop w 1 with
    lie_mem' := fun hD hE => polynomialDerivationDrop_antitone w (by decide : 1 ≤ 1 + 1)
      (polynomialDerivationDrop_bracket w 1 1 hD hE) }

abbrev PolynomialShearLieAlgebra (w : σ → ℕ) (R : Type*) [CommRing R] :=
  ↥(polynomialLoweringLieAlgebra (R := R) w)

noncomputable def polynomialShearLayer (w : σ → ℕ) (k : ℕ) :
    Submodule R (PolynomialShearLieAlgebra w R) :=
  (polynomialDerivationDrop w k).comap (polynomialLoweringLieAlgebra w).incl.toLinearMap

theorem polynomialShearLayer_antitone (w : σ → ℕ) :
    Antitone (polynomialShearLayer (R := R) w) := by
  intro a b hab D hD
  exact polynomialDerivationDrop_antitone w hab hD

theorem polynomialShearLayer_one (w : σ → ℕ) :
    polynomialShearLayer (R := R) w 1 = ⊤ := by
  apply top_unique
  intro D _
  exact D.property

theorem polynomialShearLayer_bracket (w : σ → ℕ) (a b : ℕ)
    {D E : PolynomialShearLieAlgebra w R}
    (hD : D ∈ polynomialShearLayer (R := R) w a)
    (hE : E ∈ polynomialShearLayer (R := R) w b) :
    ⁅D, E⁆ ∈ polynomialShearLayer (R := R) w (a + b) :=
  polynomialDerivationDrop_bracket w a b hD hE

theorem polynomialShearLayer_terminal (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    polynomialShearLayer (R := R) w (s + 1) = ⊥ := by
  apply bot_unique
  intro D hD
  change D = 0
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  change D.val (X i) = 0
  exact weightedSupportDrop_eq_zero (Nat.lt_succ_of_le (hw i)) (hD i)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialShearCoordinates (w : σ → ℕ) :
    PolynomialShearLieAlgebra w R ≃ₗ[R] (i : σ) → weightedSupportDrop (R := R) w (w i) 1 where
  toFun D i := ⟨D.val (X i), D.property i⟩
  invFun f := ⟨MvPolynomial.mkDerivation R (fun i => (f i : MvPolynomial σ R)), by
    intro i
    rw [MvPolynomial.mkDerivation_X]
    exact (f i).property⟩
  left_inv D := by
    apply Subtype.ext
    apply MvPolynomial.derivation_ext
    intro i
    exact MvPolynomial.mkDerivation_X _ _ _
  right_inv f := by
    funext i
    apply Subtype.ext
    exact MvPolynomial.mkDerivation_X _ _ _
  map_add' D E := by
    funext i
    apply Subtype.ext
    rfl
  map_smul' c D := by
    funext i
    apply Subtype.ext
    rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearRationalFiltration
namespace OAI

section

namespace Erdos3

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] (w : σ → ℕ)

noncomputable instance (priority := 100) polynomialShearRatLieAlgebra :
    LieAlgebra ℚ (PolynomialShearLieAlgebra w R) where
  lie_smul c D E := by
    rw [← IsScalarTower.algebraMap_smul R c E, lie_smul, IsScalarTower.algebraMap_smul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearRealGroup
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S] {w : σ → ℕ}

theorem weightedSupportDrop_map (f : R →+* S) {P : MvPolynomial σ R} {n r : ℕ}
    (hP : P ∈ weightedSupportDrop w n r) : map f P ∈ weightedSupportDrop w n r := by
  intro a ha
  exact hP (MvPolynomial.support_map_subset f P ha)

noncomputable def polynomialShearMap (f : R →+* S) (D : PolynomialShearLieAlgebra w R) :
    PolynomialShearLieAlgebra w S :=
  ⟨MvPolynomial.mkDerivation S (fun i => map f (D.val (X i))), fun i => by
    rw [MvPolynomial.mkDerivation_X]
    exact weightedSupportDrop_map f (D.property i)⟩

theorem polynomialShearMap_X (f : R →+* S) (D : PolynomialShearLieAlgebra w R) (i : σ) :
    (polynomialShearMap f D).val (X i) = map f (D.val (X i)) :=
  MvPolynomial.mkDerivation_X _ _ _

theorem polynomialShearMap_apply_map (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) :
    (polynomialShearMap f D).val (map f P) = map f (D.val P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [map_C, MvPolynomial.derivation_C, map_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, map_X, Derivation.leibniz, smul_eq_mul, map_add,
      polynomialShearMap_X, hP]

theorem polynomialShearMap_add (f : R →+* S) (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearMap f (D + E) = polynomialShearMap f D + polynomialShearMap f E := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X]
  change map f (D.val (X i) + E.val (X i)) =
    (polynomialShearMap f D).val (X i) + (polynomialShearMap f E).val (X i)
  rw [map_add, polynomialShearMap_X, polynomialShearMap_X]

theorem polynomialShearMap_smul (f : R →+* S) (c : R) (D : PolynomialShearLieAlgebra w R) :
    polynomialShearMap f (c • D) = f c • polynomialShearMap f D := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X]
  change map f (c • D.val (X i)) = f c • (polynomialShearMap f D).val (X i)
  rw [polynomialShearMap_X, ← MvPolynomial.C_mul', ← MvPolynomial.C_mul', map_mul, map_C]

theorem polynomialShearMap_lie (f : R →+* S) (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearMap f ⁅D, E⁆ = ⁅polynomialShearMap f D, polynomialShearMap f E⁆ := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X]
  change map f (D.val (E.val (X i)) - E.val (D.val (X i))) =
    (polynomialShearMap f D).val ((polynomialShearMap f E).val (X i)) -
      (polynomialShearMap f E).val ((polynomialShearMap f D).val (X i))
  rw [map_sub, polynomialShearMap_X, polynomialShearMap_X,
    polynomialShearMap_apply_map, polynomialShearMap_apply_map]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {σ : Type*} (w : σ → ℕ)

noncomputable def polynomialShearRationalRealMap :
    PolynomialShearLieAlgebra w ℚ →ₗ[ℚ] PolynomialShearLieAlgebra w ℝ where
  toFun := polynomialShearMap (algebraMap ℚ ℝ)
  map_add' := polynomialShearMap_add _
  map_smul' c D := by
    rw [polynomialShearMap_smul]
    exact IsScalarTower.algebraMap_smul ℝ c _

noncomputable def polynomialShearRealificationMap :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) →ₗ[ℝ] PolynomialShearLieAlgebra w ℝ :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℝ _ (polynomialShearRationalRealMap w))

theorem polynomialShearRealificationMap_tmul (r : ℝ) (D : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearRealificationMap w (r ⊗ₜ[ℚ] D) =
      r • polynomialShearMap (algebraMap ℚ ℝ) D := rfl

noncomputable def polynomialShearRealificationHom :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) →ₗ⁅ℝ⁆ PolynomialShearLieAlgebra w ℝ where
  toLinearMap := polynomialShearRealificationMap w
  map_lie' := by
    intro x y
    change polynomialShearRealificationMap w ⁅x, y⁆ =
      ⁅polynomialShearRealificationMap w x, polynomialShearRealificationMap w y⁆
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r D =>
      induction y using TensorProduct.induction_on with
      | zero =>
        refine (congrArg _ (lie_zero (L := ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
          (M := ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) _)).trans ?_
        first | (simp; done) | (rw [map_zero]; exact (lie_zero (L := PolynomialShearLieAlgebra w ℝ)
          (M := PolynomialShearLieAlgebra w ℝ) _).symm)
      | tmul t E =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, polynomialShearRealificationMap_tmul,
          polynomialShearMap_lie, smul_lie, lie_smul, smul_smul, mul_comm]
      | add y z hy hz => simp only [LieRing.lie_add, map_add, hy, hz]
    | add x z hx hz => simp only [LieRing.add_lie, map_add, hx, hz]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationShearExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

theorem scalarDirectionalDerivative_weight_drop (w : σ → ℕ) (x : σ → ℚ) (k : ℕ)
    (hx : ∀ i, w i < k → x i = 0) {n r : ℕ} {P : MvPolynomial σ ℚ}
    (hP : P ∈ weightedSupportDrop w n r) :
    scalarDirectionalDerivative x P ∈ weightedSupportDrop w n (r + k) := by
  apply weightedDerivation_apply w (scalarDirectionalDerivative x) k _ hP
  intro i
  rw [scalarDirectionalDerivative_X]
  by_cases hi : k ≤ w i
  · exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simpa using hi))
  · rw [hx i (by omega), map_zero]
    exact Submodule.zero_mem _

namespace PolynomialTranslationLie

theorem weightedLayer_lie_mem (w : σ → ℕ) (d : ℕ) {i j : ℕ}
    {x y : PolynomialTranslationLie σ} (hx : x ∈ weightedLayer w d i)
    (hy : y ∈ weightedLayer w d j) : ⁅x,y⁆ ∈ weightedLayer w d (i+j) := by
  refine ⟨by simp, ?_⟩
  change scalarDirectionalDerivative x.base y.polynomial -
    scalarDirectionalDerivative y.base x.polynomial ∈ _
  apply Submodule.sub_mem
  · simpa only [Nat.add_comm j i] using scalarDirectionalDerivative_weight_drop w x.base i hx.1 hy.2
  · exact scalarDirectionalDerivative_weight_drop w y.base j hy.1 hx.2

noncomputable def weightedSubalgebra (w : σ → ℕ) (d : ℕ) : LieSubalgebra ℚ (PolynomialTranslationLie σ) :=
  { weightedLayer w d 1 with
    lie_mem' := fun hx hy => weightedLayer_antitone w d (by omega : 1 ≤ 1+1)
      (weightedLayer_lie_mem w d hx hy) }

@[simp] theorem mem_weightedSubalgebra (w : σ → ℕ) (d : ℕ) (x : PolynomialTranslationLie σ) :
    x ∈ weightedSubalgebra w d ↔ x ∈ weightedLayer w d 1 := Iff.rfl

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

noncomputable def shearDerivation (x : PolynomialTranslationLie σ) :
    Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ) (MvPolynomial (σ ⊕ Unit) ℚ) :=
  mkDerivation ℚ (Sum.elim (fun i => C (x.base i)) (fun _ => rename Sum.inl x.polynomial))

omit [Fintype σ] in
@[simp] theorem shearDerivation_X_inl (x : PolynomialTranslationLie σ) (i : σ) :
    shearDerivation x (X (Sum.inl i)) = C (x.base i) := mkDerivation_X _ _ _

omit [Fintype σ] in
@[simp] theorem shearDerivation_X_inr (x : PolynomialTranslationLie σ) (u : Unit) :
    shearDerivation x (X (Sum.inr u)) = rename Sum.inl x.polynomial := mkDerivation_X _ _ _

theorem shearDerivation_rename (x : PolynomialTranslationLie σ) (P : MvPolynomial σ ℚ) :
    shearDerivation x (rename Sum.inl P) =
      rename Sum.inl (scalarDirectionalDerivative x.base P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.derivation_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, rename_X, Derivation.leibniz, smul_eq_mul,
        shearDerivation_X_inl, scalarDirectionalDerivative_X, map_add, rename_C, hP]

noncomputable def shearDerivationHom : PolynomialTranslationLie σ →ₗ⁅ℚ⁆
    Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ) (MvPolynomial (σ ⊕ Unit) ℚ) where
  toFun := shearDerivation
  map_add' x y := by
    apply MvPolynomial.derivation_ext
    intro i
    cases i <;> simp [Pi.add_apply]
  map_smul' r x := by
    apply MvPolynomial.derivation_ext
    intro i
    cases i <;> simp [Derivation.smul_apply, Pi.smul_apply, Algebra.smul_def]
  map_lie' := by
    intro x y
    apply MvPolynomial.derivation_ext
    intro i
    cases i <;> simp [Derivation.commutator_apply, MvPolynomial.derivation_C,
      shearDerivation_rename]

omit [Fintype σ] in

theorem shearDerivation_mem_drop (w : σ → ℕ) (d k : ℕ)
    {x : PolynomialTranslationLie σ} (hx : x ∈ weightedLayer w d k) :
    shearDerivation x ∈ polynomialDerivationDrop (shearWeight w d) k := by
  intro i
  cases i with
  | inl i =>
      rw [shearDerivation_X_inl]
      by_cases hi : k ≤ w i
      · exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simpa [shearWeight] using hi))
      · rw [hx.1 i (by omega), map_zero]
        exact Submodule.zero_mem _
  | inr u =>
      rw [shearDerivation_X_inr]
      exact weightedSupportDrop_rename Sum.inl (fun _ => rfl) hx.2

noncomputable def weightedShearEmbedding (w : σ → ℕ) (d : ℕ) :
    weightedSubalgebra w d →ₗ⁅ℚ⁆ PolynomialShearLieAlgebra (shearWeight w d) ℚ where
  toFun x := ⟨shearDerivationHom x.val, shearDerivation_mem_drop w d 1 x.property⟩
  map_add' x y := Subtype.ext (shearDerivationHom.map_add x.val y.val)
  map_smul' r x := Subtype.ext (shearDerivationHom.map_smul r x.val)
  map_lie' := by
    intro x y
    exact Subtype.ext (shearDerivationHom.map_lie x.val y.val)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineSubstitution
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem integerAffinePolynomial_support (A : σ → τ → ℤ) (b : σ → ℤ) (i : σ) :
    integerAffinePolynomial A b i ∈ weightedSupportLE (fun _ : τ => 1) 1 := by
  apply Submodule.add_mem
  · exact weightedSupportLE_C _ 1 (b i : ℚ)
  · apply Submodule.sum_mem
    intro j _
    have hx : (MvPolynomial.X j : MvPolynomial τ ℚ) ∈ weightedSupportLE (fun _ : τ => 1) 1 := by
      simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
        weightedSupportLE_monomial (fun _ : τ => 1) (Finsupp.single j 1) (1 : ℚ)
    simpa only [zero_add] using weightedSupportLE_mul (weightedSupportLE_C _ 0 (A i j : ℚ)) hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteDensityMassBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteSupportProbability {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x) :
    FiniteProbabilityWeights S where
  weight x := w x.val / ∑' y, w y
  nonneg x := div_nonneg (hw0 x.val) hZ.le
  total := by
    rw [← Finset.sum_div, sum_support_eq_tsum w S hw, div_self hZ.ne']

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

noncomputable def residueSmoothWeight {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (V : K × I → ℝ) (y : K × I → ℤ) : ℝ := by
  classical
  exact if ∀ z, (modulus z.2 : ℤ) ∣ y z - residue z then
    smoothProductProfile (K × I) (fun z => (y z : ℝ) / V z) else 0

end Erdos3

end

section

namespace Erdos3

def columnResiduePattern {K I : Type*} (modulus : I → ℕ) (x : K × I → ℤ) :
    ColumnResiduePattern K I modulus := fun z => x z

noncomputable def columnResidueRepresentative {K I : Type*} (modulus : I → ℕ)
    (r : ColumnResiduePattern K I modulus) : K × I → ℤ :=
  fun z => (ZMod.intCast_surjective (r z)).choose

theorem columnResidueRepresentative_cast {K I : Type*} (modulus : I → ℕ)
    (r : ColumnResiduePattern K I modulus) (z : K × I) :
    (columnResidueRepresentative modulus r z : ZMod (modulus z.2)) = r z :=
  (ZMod.intCast_surjective (r z)).choose_spec

theorem columnResiduePattern_eq_iff {K I : Type*} (modulus : I → ℕ)
    (r : ColumnResiduePattern K I modulus) (x : K × I → ℤ) :
    columnResiduePattern modulus x = r ↔
      ∀ z, (modulus z.2 : ℤ) ∣ x z - columnResidueRepresentative modulus r z := by
  constructor
  · intro he z
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, columnResidueRepresentative_cast]
    exact sub_eq_zero.mpr (congrFun he z)
  · intro h
    funext z
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h z)
    rw [Int.cast_sub, columnResidueRepresentative_cast, sub_eq_zero] at hz
    exact hz

theorem residueSmoothWeight_eq_pattern {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (r : ColumnResiduePattern K I modulus)
    (V : K × I → ℝ) (x : K × I → ℤ) :
    residueSmoothWeight (columnResidueRepresentative modulus r) modulus V x =
      if columnResiduePattern modulus x = r then
        smoothProductProfile (K × I) (fun z => (x z : ℝ) / V z) else 0 := by
  classical
  simp only [residueSmoothWeight, ← columnResiduePattern_eq_iff]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def selectedResidueSmoothWeight {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (x : K × I → ℤ) : ℝ :=
  if columnResiduePattern modulus x ∈ G then
    smoothProductProfile (K × I) (fun z => (x z : ℝ) / V z) else 0

theorem selectedResidueSmoothWeight_eq_sum {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (x : K × I → ℤ) :
    selectedResidueSmoothWeight modulus G V x =
      ∑ r : G, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
  symm
  calc
    _ = ∑ r ∈ G, residueSmoothWeight (columnResidueRepresentative modulus r) modulus V x :=
      Finset.sum_coe_sort G (fun r => residueSmoothWeight (columnResidueRepresentative modulus r) modulus V x)
    _ = _ := by
      simp only [residueSmoothWeight_eq_pattern, Finset.sum_ite_eq, selectedResidueSmoothWeight]

theorem residueSmoothWeight_zero_off {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (x : K × I → ℤ) (hx : x ∉ rectangularWeightIndices 0 V 1) :
    residueSmoothWeight residue modulus V x = 0 := by
  have hz := rectangularWeight_zero_off_indices (smoothProductProfile (K × I)) 0 V hV
    (smoothProductProfile_zero_outside (K × I)) x hx
  simp only [rectangularWeight, rectangularLatticePoint_zero_origin] at hz
  simp only [residueSmoothWeight, hz, ite_self]

theorem selectedResidueSmoothWeight_nonneg {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (x : K × I → ℤ) : 0 ≤ selectedResidueSmoothWeight modulus G V x := by
  unfold selectedResidueSmoothWeight
  split
  · exact (smoothProductProfile_range (K × I) _).1
  · exact le_rfl

theorem selectedResidueSmoothWeight_zero_off {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (x : K × I → ℤ) (hx : x ∉ rectangularWeightIndices 0 V 1) :
    selectedResidueSmoothWeight modulus G V x = 0 := by
  rw [selectedResidueSmoothWeight_eq_sum]
  simp only [residueSmoothWeight_zero_off _ _ V hV x hx, Finset.sum_const_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

@[simp] theorem basisGradeProjection_repr (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) (i : ι) :
    b.repr (basisGradeProjection b w j x) i = if w i = j then b.repr x i else 0 :=
  basisCoordinateProjection_repr b {i | w i = j} x i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedLieUpperSpan
namespace OAI

section

namespace Erdos3

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

def weightedLieUpperGenerators (v : I → L) (w : I → ℕ) (d : ℕ) : Set L :=
  {x | ∃ a : FreeMagma I, d ≤ lieTreeWeight w a ∧ lieTreeEval v a = x}

def weightedLieUpperSpan (v : I → L) (w : I → ℕ) (d : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ (weightedLieUpperGenerators v w d)

theorem weightedLieUpperSpan_lie_mem (v : I → L) (w : I → ℕ) {d e : ℕ} {x y : L}
    (hx : x ∈ weightedLieUpperSpan v w d) (hy : y ∈ weightedLieUpperSpan v w e) :
    ⁅x, y⁆ ∈ weightedLieUpperSpan v w (d + e) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, Nat.add_le_add ha hb, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

omit [Fintype σ] in
@[simp] theorem scalarDirectionalDerivative_linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (i : σ) :
    scalarDirectionalDerivative z (linearCoordinatePolynomial A i) = C (A z i) := by
  classical
  rw [linearCoordinatePolynomial, map_sum]
  simp only [Derivation.map_smul, scalarDirectionalDerivative_X]
  simp only [← C_mul', ← map_mul]
  rw [← map_sum, linearMap_apply_sum_coordinates]

omit [Fintype σ] in
theorem eval_polynomialLinearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (x : τ → ℚ) (P : MvPolynomial σ ℚ) :
    eval x (polynomialLinearRestriction A P) = eval (A x) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
namespace OAI

section

namespace Erdos3

variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

namespace DegreeRankLieFiltration

variable {L} {s r : ℕ} (F : DegreeRankLieFiltration L s r)

theorem rank_antitone (d : ℕ) : Antitone (F.layer d) := by
  intro i j hij
  exact F.lex_antitone (Or.inr ⟨rfl, hij⟩)

end DegreeRankLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem basis_reindex_equivFun_symm (b : Basis ι ℚ L) (e : ι ≃ κ) (x : κ → ℚ) :
    (b.reindex e).equivFun.symm x = b.equivFun.symm (fun i => x (e i)) := by
  apply b.equivFun.injective
  funext i
  rw [LinearEquiv.apply_symm_apply]
  have h := congrFun ((b.reindex e).equivFun.apply_symm_apply x) (e i)
  simpa only [Basis.equivFun_apply, Basis.repr_reindex_apply,
    Equiv.symm_apply_apply] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3

noncomputable def scalarAffinePolynomial {σ : Type*} (r : ℚ) (shift : σ → ℚ) (i : σ) :
    MvPolynomial σ ℚ := MvPolynomial.C (shift i) + MvPolynomial.C r * MvPolynomial.X i

end Erdos3

end

end OAI
end


