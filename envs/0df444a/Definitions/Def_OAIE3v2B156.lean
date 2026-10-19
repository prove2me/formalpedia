-- Prove2me | Definitions.Def_OAIE3v2B156
-- name    : OAIE3v2B156
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:24:55.299792+00:00
-- url     : https://prove2.me/theorems/f2079845-4283-4f15-9348-03128c3d2486
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 158 of 311
-- statement:
--   Definitions bundle 158 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B140`, `OAIE3v2B141`, `OAIE3v2B142`, `OAIE3v2B144`, `OAIE3v2B145`, `OAIE3v2B146` of this split.
--
--   Modules: `Estimates/FormalCurrentInputBounds.lean`, `Estimates/NativeResidualMultiplier.lean`, `Estimates/RationalFormalStageGeometry.lean`, `Estimates/RealFirstCoefficientHorizontal.lean`, `Estimates/RealReducedCoefficientMap.lean`, `Estimates/ReducedDiagonalBounds.lean`, `Estimates/ReducedNativeFactorization.lean`, `Estimates/UniformFormalCurrentLayerStep.lean`, `Fourier/BohrNiltestBudget.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Linear/StepDropBasisBudget.lean`, `Polynomial/ControlledCurrentLayerPolynomialStep.lean`, `Polynomial/PolynomialLiftArrays.lean`, `Sampling/RealAdaptedCoefficientGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B140
import Definitions.Def_OAIE3v2B141
import Definitions.Def_OAIE3v2B142
import Definitions.Def_OAIE3v2B144
import Definitions.Def_OAIE3v2B145
import Definitions.Def_OAIE3v2B146

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialLiftArrays
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

open VectorPolynomial

variable {σ κ ι L : Type*} [Fintype κ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {V : Submodule ℚ L}

theorem liftQuotientArray_coefficient_eq_zero (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ)
    (hS : ∀ t, coefficients (S t) α = 0) : coefficients (liftQuotientArray f S) α = 0 := by
  funext bi
  rw [coefficients_liftQuotientArray, hS, map_zero]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

theorem realAdaptedDirectionalDerivative_bound (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T M x)
    (hh : ∀ i, |(h i : ℝ)| ≤ T i) :
    F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T ((Fintype.card σ : ℝ) * s * M)
      (F.realAdaptedDirectionalDerivative h x) := by
  have hp := (F.realAdaptedCoefficientBound_polynomial_iff b ω hF (fun _ => 1) T hT hM
    (⟨x⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1))).mp hx
  intro z
  rw [← F.realAdaptedPolynomialTensor_coordinates (fun _ => 1) b ω hF,
    F.realAdaptedDirectionalDerivative_polynomial]
  let f := ((b.baseChange ℝ).coord z.val.2).restrictScalars ℚ
  have hdegree : ∀ (β : σ →₀ ℕ) (j : σ), s < β j →
      f (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) β) = 0 := by
    intro β j hj
    have hβ := Finsupp.le_weight (fun _ : σ => 1) (s := j) (by decide) β
    have hi := F.adaptedBasis_weight_le_step b ω hF z.val.2
    have hni : ¬ Finsupp.weight (fun _ : σ => 1) β ≤ ω z.val.2 := by omega
    exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
      ((F.realification.adapted_iff_coefficients (fun _ => 1) _).mp
        (F.realAdaptedPolynomialMap_adapted (fun _ => 1) x) β) z.val.2 hni
  exact directionalDerivative_scaled_coordinate_bound f
    (F.realAdaptedPolynomialMap (fun _ => 1) x) s hdegree T hT M hM
    (fun β => hp β z.val.2) h hh z.val.1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

theorem exists_real_adapted_log_derivative_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1),
      F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + 2) ^ a)) x →
      ∀ h : σ → ℚ, (∀ i, |(h i : ℝ)| ≤ T i) →
      F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
        (F.realAdaptedLogDerivative h x) := by
  have hoperationsExists := exists_scaled_polynomial_dual_bound s 1
  obtain ⟨c, _, hoperations⟩ := hoperationsExists
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a +
    Polynomial.C (s + 1) * (Polynomial.X + 1) + Polynomial.X + 2
  let B : Polynomial ℕ := (Q + Polynomial.C c) ^ c
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc T hT x hx h hh
  let t := (s + 1 : ℝ) * (p + 1)
  let q := (p + 2) ^ a + t + p + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ha : 0 ≤ (p + 2) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + 2) ^ a ≤ q + 2 := by dsimp [q]; linarith
  have hfinal : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, Q, q, t, Polynomial.eval₂_pow] using hbound p hp
  have hfactor : (Fintype.card σ : ℝ) * s ≤ Real.exp t := by
    have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
    have hmul := mul_le_mul_of_nonneg_right hσ hs
    have hsmall : (Fintype.card σ : ℝ) * s ≤ t := by dsimp [t]; nlinarith
    exact hsmall.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp t))
  have hgain : (Fintype.card σ : ℝ) * s * Real.exp ((p + 2) ^ a) ≤ Real.exp (q + 2) := by
    apply (mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [q]
    linarith
  have hvalue := F.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr haq) x hx
  have hderivative := F.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT hgain
    (F.realAdaptedDirectionalDerivative h x)
    (F.realAdaptedDirectionalDerivative_bound h b ω hF T hT (Real.exp_nonneg _) x hx hh)
  have hdual := (hoperations F b ω hF (fun _ : σ => 1) (by simp) H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq)) hc T hT).1
    (F.realAdaptedPolynomialJet h x)
    (by simpa only [F.realAdaptedPolynomialJet_base, pow_one] using hvalue)
    (by simpa only [F.realAdaptedPolynomialJet_tangent, pow_one] using hderivative)
  exact F.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr hfinal) _ hdual

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealAdaptedCoefficientGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedCoefficientGrid_mono {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hx : F.RealAdaptedCoefficientGrid b ω hF w l x) :
    F.RealAdaptedCoefficientGrid b ω hF w m x :=
  realDenominatorGrid_subset_of_dvd hl hlm hx

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalCurrentInputBounds
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {L μ ι σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] {V : Submodule ℚ L}

theorem projected_polynomial_coefficient_bound (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (j : ℕ) {H : ℕ}
    (hf : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : CoefficientBound (b.baseChange ℝ) T M P)
    (α : σ →₀ ℕ) :
    ‖realQuotientCoordinateMap f (coefficients
      (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P) α)‖ ≤
      (((Fintype.card μ : ℝ) + 1) * (H + 1)) * M / monomialScale T α := by
  rw [coefficients_map]
  let C : ℝ := ((Fintype.card μ : ℝ) + 1) * (H + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb := (coefficientBound_iff_norm (b.baseChange ℝ) T hT hM P).mp hP α
  calc
    _ ≤ C * ‖(b.baseChange ℝ).equivFun
        (basisGradeProjection (b.baseChange ℝ) w j (coefficients P α))‖ :=
      realQuotientCoordinateMap_norm_bound b f hf _
    _ ≤ C * ‖(b.baseChange ℝ).equivFun (coefficients P α)‖ :=
      mul_le_mul_of_nonneg_left (basisCoordinateProjection_norm_le (b.baseChange ℝ) {z | w z = j} _) hC
    _ ≤ C * (M / monomialScale T α) := mul_le_mul_of_nonneg_left hb hC
    _ = _ := by ring

theorem projected_polynomial_coefficient_grid (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (j l : ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : CoefficientGrid (b.baseChange ℝ) l P)
    (α : σ →₀ ℕ) :
    realQuotientCoordinateMap f (coefficients
      (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P) α) ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  rw [coefficients_map]
  apply realQuotientCoordinateMap_grid b f l
  exact basisCoordinateProjection_real_grid (b.baseChange ℝ) {z | w z = j} l _ (hP α)

theorem uniform_current_layer_inputs_from_ambient (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (j : ℕ) {H l : ℕ}
    (hl : 0 < l) (hf : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hambient : (Fintype.card μ : ℝ) ≤ p)
    (hquotient : (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i))
    (hrational : ∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp (bracketConstructionBudget p) ∧
      (∀ i α, ‖realQuotientCoordinateMap f (coefficients
        (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
          Real.exp (bracketConstructionBudget p) / (T i * monomialScale T α)) ∧
      ∀ i α, realQuotientCoordinateMap f (coefficients
        (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
          realDenominatorGrid n := by
  let n := matrixDenominator (quotientCoordinateMatrix b f) * l
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos _) hl
  obtain ⟨_, _, hdenCap, hnormCap⟩ := bracket_construction_budget_bounds hp
  have hD := matrixDenominator_le_exp_power (quotientCoordinateMatrix b f) hp 1 hquotient hambient
    (fun i z => (show (((quotientCoordinateMatrix b f i z).den) : ℝ) ≤ H from Nat.cast_le.mpr (hf i z).2).trans
      (hHp.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))))
  have hnbound : (n : ℝ) ≤ Real.exp (bracketConstructionBudget p) := by
    calc
      _ = (matrixDenominator (quotientCoordinateMatrix b f) : ℝ) * (l : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp p :=
        mul_le_mul hD hlp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdenCap
  have hfactor : (((Fintype.card μ : ℝ) + 1) * (H + 1)) * Real.exp p ≤
      Real.exp (bracketConstructionBudget p) := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp p :=
        mul_le_mul_of_nonneg_right (current_layer_coordinate_factor_bound hp _ H hambient hHp) (Real.exp_nonneg _)
      _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hnormCap
  refine ⟨n, hn, hnbound, ?_, fun i α => projected_polynomial_coefficient_grid b w f j l _ (hrational i) α⟩
  intro i α
  have h := projected_polynomial_coefficient_bound b w f j hf T hT
    (div_nonneg (Real.exp_nonneg p) (hT i).le) (small i) (hsmall i) α
  calc
    _ ≤ (((Fintype.card μ : ℝ) + 1) * (H + 1)) * (Real.exp p / T i) / monomialScale T α := h
    _ = ((((Fintype.card μ : ℝ) + 1) * (H + 1)) * Real.exp p) / (T i * monomialScale T α) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hfactor (mul_nonneg (hT i).le (monomialScale_pos T hT α).le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d t : ℕ}

noncomputable def torusPhaseLinear (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (Fin t → ℝ) :=
  ((RationalTorus.basis t).baseChange ℝ).equivFun.toLinearMap.comp (φ.toLinearMap.baseChange ℝ)

variable (D : RationalFilteredNilmanifold L s d) (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)

theorem torusPhaseLinear_inv (g : D.RealGroup) :
    torusPhaseLinear φ g⁻¹.coord = -torusPhaseLinear φ g.coord :=
  (torusPhaseLinear φ).map_neg g.coord

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeIntegerModelFamily.lie NativeIntegerModelFamily.algebra
  NativeIntegerModelFamily.topology NativeIntegerModelFamily.topologicalAdd
  NativeIntegerModelFamily.continuousSMul NativeIntegerModelFamily.hausdorff

namespace NativeIntegerExpansion

variable {σ : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ} {f : (σ → ℤ) → ℂ}

noncomputable def ofModelFamily {I : Type*} {g : I → (σ → ℤ) → ℂ}
    (R : NativeIntegerModelFamily w s p g) (i : I) :
    NativeIntegerExpansion w s p (g i) :=
  ofTest (R.test i) (R.complexity i) (fun x => (R.eval i x).symm)

end NativeIntegerExpansion

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

namespace NativeIntegerVectorEquivalence

theorem linearPullbackHom {σ τ J K : Type*} [Fintype τ] [Fintype J] [Fintype K]
    {s : ℕ} {p : ℝ} {f : J → (σ → ℤ) → ℂ} {g : K → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (A : σ → ((τ → ℤ) →+ ℤ)) :
    NativeIntegerVectorEquivalence s p
      (fun j x => f j (fun i => A i x)) (fun k x => g k (fun i => A i x)) where
  left_dimension := E.left_dimension
  right_dimension := E.right_dimension
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.linearPullbackHom A⟩

end NativeIntegerVectorEquivalence

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
  (E : NativeIntegerVectorEquivalence s p chi eta)

abbrev ExpansionIndex := Σ j : J, Σ k : K, Fin (E.selectedExpansion j k).count

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalFormalStageGeometry
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem exists_rational_formal_stage_geometry
    {L μ υ χ ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype ι] [Fintype κ]
    (b : Basis μ ℚ L) (w : μ → ℕ) (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (hU : BasisGradedSubmodule b w U.toSubmodule)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (f : Basis ι ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H r : ℕ} (hH : 1 ≤ H)
    (hrU : 2 * Fintype.card υ + Fintype.card μ ≤ r)
    (hrK : Fintype.card υ + Fintype.card χ + Fintype.card μ ≤ r)
    (hrV : Fintype.card υ + Fintype.card ι + Fintype.card μ ≤ r)
    (hQU : ∀ i z, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b z)) i) H)
    (hQK : ∀ i z, RationalHeightLE (fK.repr (K.mkQ (b z)) i) H)
    (hQV : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (hK : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (hstructure : ∀ i z k, RationalHeightLE (b.repr ⁅b i, b z⁆ k) H)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ G : FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j
      (formalGeometryHeight (Fintype.card μ) r H),
      G.bracketRank ≤ Fintype.card μ ∧ G.currentRank ≤ Fintype.card μ := by
  classical
  let J := homogeneousIntersectionBasisHeight (Fintype.card μ) r H
  let M := max H J
  let B := if j = 2 then K else V
  let Ebr := homogeneousIntersection b w (j - 1) U.toSubmodule B
  let Ecur := homogeneousIntersection b w j U.toSubmodule U.toSubmodule
  have hMout : M ≤ formalGeometryHeight (Fintype.card μ) r H := Nat.le_max_left _ _
  have hHout : H ≤ formalGeometryHeight (Fintype.card μ) r H := (Nat.le_max_left H J).trans hMout
  have hJout : J ≤ formalGeometryHeight (Fintype.card μ) r H := (Nat.le_max_right H J).trans hMout
  obtain ⟨eBr, heBr⟩ : ∃ e : Basis (Fin (Module.finrank ℚ Ebr)) ℚ Ebr,
      ∀ i z, RationalHeightLE (b.repr (e z : L) i) J := by
    by_cases hj2 : j = 2
    · obtain ⟨e, he⟩ := exists_homogeneousIntersection_basis b w (j - 1) U.toSubmodule K fU fK hH hrK hQU hQK
      have hE : Ebr = homogeneousIntersection b w (j - 1) U.toSubmodule K :=
        congrArg (homogeneousIntersection b w (j - 1) U.toSubmodule) (show B = K from if_pos hj2)
      rw [hE]
      exact ⟨e, fun i z => he z i⟩
    · obtain ⟨e, he⟩ := exists_homogeneousIntersection_basis b w (j - 1) U.toSubmodule V fU f hH hrV hQU hQV
      have hE : Ebr = homogeneousIntersection b w (j - 1) U.toSubmodule V :=
        congrArg (homogeneousIntersection b w (j - 1) U.toSubmodule) (show B = V from if_neg hj2)
      rw [hE]
      exact ⟨e, fun i z => he z i⟩
  obtain ⟨eCur, heCur⟩ := exists_homogeneousIntersection_basis b w j U.toSubmodule U.toSubmodule fU fU (r := r)
    hH (by omega) hQU hQU
  have hbrmem (x : ℝ ⊗[ℚ] L) : x ∈ Ebr.baseChange ℝ ↔
      x ∈ realificationLieSubalgebra U ∧ x ∈ B.baseChange ℝ ∧
      basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x := by
    rw [homogeneousIntersection_baseChange]
    exact mem_homogeneousIntersection _ _ _ _ _ _
  have hcurmem (x : ℝ ⊗[ℚ] L) : x ∈ Ecur.baseChange ℝ ↔
      x ∈ realificationLieSubalgebra U ∧ x ∈ realificationLieSubalgebra U ∧
      basisGradeProjection (b.baseChange ℝ) w j x = x := by
    rw [homogeneousIntersection_baseChange]
    exact mem_homogeneousIntersection _ _ _ _ _ _
  let G : FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j
      (formalGeometryHeight (Fintype.card μ) r H) := {
    bracketSpace := Ebr
    currentSpace := Ecur
    bracketRank := Module.finrank ℚ Ebr
    currentRank := Module.finrank ℚ Ecur
    bracketBasis := eBr
    currentBasis := eCur
    bracket_grade := fun x hx => (hbrmem x).mp hx |>.2.2
    bracket_U := fun x hx => (hbrmem x).mp hx |>.1
    bracket_K := by
      intro h x hx
      simpa only [B, if_pos h] using ((hbrmem x).mp hx).2.1
    bracket_V := by
      intro h x hx
      simpa only [B, if_neg (show j ≠ 2 by omega)] using ((hbrmem x).mp hx).2.1
    bracket_complete := by
      intro x hx hgrade hKx hVx
      apply (hbrmem x).mpr
      refine ⟨hx, ?_, hgrade⟩
      by_cases h : j = 2
      · simpa only [B, if_pos h] using hKx h
      · simpa only [B, if_neg h] using hVx (by omega)
    current_grade := fun x hx => (hcurmem x).mp hx |>.2.2
    current_U := fun x hx => (hcurmem x).mp hx |>.1
    current_projection := by
      intro x hx
      apply (hcurmem _).mpr
      have hp := hU.baseChange b w U.toSubmodule j x hx
      exact ⟨hp, hp, basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j} x⟩
    bracket_matrix_height := by
      intro i z
      have h := bracketSystemMatrix_height b eBr f (fun k => (eK k : L))
        (fun i j k => (hstructure i j k).mono (Nat.le_max_left H J))
        (fun z i => (heBr i z).mono (Nat.le_max_right H J))
        (fun z i => (hK i z).mono (Nat.le_max_left H J))
        (fun i k => (hQV k i).mono (Nat.le_max_left H J)) i z
      exact h.mono ((Nat.le_max_right (formalCurrentMatrixHeight (Fintype.card μ) M)
        (formalBracketMatrixHeight (Fintype.card μ) M)).trans (Nat.le_max_right _ _))
    current_matrix_height := by
      intro i z
      have h := subspaceQuotientMatrix_height b eCur f
        (fun i k => (hQV k i).mono (Nat.le_max_left H J))
        (fun z i => (heCur z i).mono (Nat.le_max_right H J)) i z
      exact h.mono ((Nat.le_max_left (formalCurrentMatrixHeight (Fintype.card μ) M)
        (formalBracketMatrixHeight (Fintype.card μ) M)).trans (Nat.le_max_right _ _))
    bracket_basis_height := fun i z => (heBr i z).mono hJout
    current_basis_height := fun i z => (heCur z i).mono hJout }
  exact ⟨G, homogeneousIntersection_finrank_le b w (j - 1) U.toSubmodule B,
    homogeneousIntersection_finrank_le b w j U.toSubmodule U.toSubmodule⟩

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareRealRelativePart_mul
    (g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.reducedSquareRealRelativePart w (g * h) = F.reducedSquareRealRelativePart w g *
      (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g) *
        F.reducedSquareRealRelativePart w h *
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g))⁻¹) :=
  splitRelativePart_mul _ _ g h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem reducedSquareRealRelativePart_exists_preimage
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    ∃ p : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w,
      F.realReducedRelativeSquareSymbolMap w hw p = (F.reducedSquareRealRelativePart w g).coord := by
  change (F.reducedSquareRealRelativePart w g).coord ∈
    LinearMap.range (F.realReducedRelativeSquareSymbolMap w hw)
  rw [F.realReducedRelativeSquareSymbolMap_range]
  exact F.reducedSquareRealRelativePart_coord_kernel w g

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "bq" => F.quotientTopBasis b ω hF
local notation "ωq" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "hq" => F.quotientTopBasis_layers b ω hF
local notation "Bq" => F.quotientTop.polynomialSymbolBasis bq ωq hq w
local notation "Ba" => F.adaptedMonomialBasis b ω hF w

theorem reducedNativeSection_coordinate (x : F.quotientTop.PolynomialSymbol w)
    (z : SymbolBasisIndex w ωq) :
    (Ba).repr (F.reducedNativeSection b ω hF w x) (reducedNativeIndex s w ω z) = (Bq).repr x z := by
  classical
  have he : ((Ba).coord (reducedNativeIndex s w ω z)).comp (F.reducedNativeSection b ω hF w) =
      (Bq).coord z := by
    apply (Bq).ext
    intro j
    change (Ba).repr (F.reducedNativeSection b ω hF w (Bq j)) (reducedNativeIndex s w ω z) =
      (Bq).repr (Bq j) z
    rw [F.reducedNativeSection_basis, Basis.repr_self, Basis.repr_self]
    simp only [Finsupp.single_apply, (reducedNativeIndex_injective s w ω).eq_iff]
  exact DFunLike.congr_fun he x

theorem reducedNativeSection_coordinate_zero (x : F.quotientTop.PolynomialSymbol w)
    (z : AdaptedBasisIndex w ω)
    (hz : ∀ j, reducedNativeIndex s w ω j ≠ z) :
    (Ba).repr (F.reducedNativeSection b ω hF w x) z = 0 := by
  classical
  have he : ((Ba).coord z).comp (F.reducedNativeSection b ω hF w) = 0 := by
    apply (Bq).ext
    intro j
    change (Ba).repr (F.reducedNativeSection b ω hF w (Bq j)) z = 0
    rw [F.reducedNativeSection_basis, Basis.repr_self]
    exact Finsupp.single_eq_of_ne (hz j).symm
  exact DFunLike.congr_fun he x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "bq" => F.quotientTopBasis b ω hF
local notation "ωq" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "hq" => F.quotientTopBasis_layers b ω hF
local notation "Bq" => F.quotientTop.polynomialSymbolBasis bq ωq hq w
local notation "Ba" => F.adaptedMonomialBasis b ω hF w

theorem reducedNativeSection_real_coordinate (x : F.quotientTop.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w ωq) :
    ((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ x)
      (reducedNativeIndex s w ω z) = ((Bq).baseChange ℝ).repr x z := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul,
      F.reducedNativeSection_coordinate]

theorem reducedNativeSection_real_coordinate_zero (x : F.quotientTop.RealPolynomialSymbol w)
    (z : AdaptedBasisIndex w ω) (hz : ∀ j, reducedNativeIndex s w ω j ≠ z) :
    ((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ x) z = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      F.reducedNativeSection_coordinate_zero b ω hF w x z hz]
    simp

theorem realReducedNativeLift_constant (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    coefficients (F.realAdaptedPolynomialMap w (F.realReducedNativeLift b ω hF w g).coord) 0 = 0 := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  change (b.baseChange ℝ).repr
    (coefficients (F.realAdaptedPolynomialMap w (F.realReducedNativeLift b ω hF w g).coord) 0) i = 0
  let z : AdaptedBasisIndex w ω := ⟨(0, i), by simp⟩
  have hz : ∀ j, reducedNativeIndex s w ω j ≠ z := by
    intro j hj
    have hmono := congrArg (fun t : AdaptedBasisIndex w ω => Finsupp.weight w t.val.1) hj
    change Finsupp.weight w j.val.1 = Finsupp.weight w 0 at hmono
    rw [map_zero] at hmono
    exact (F.adaptedBasis_weight_pos b ω hF j.val.2.val).ne' (j.property.symm.trans hmono)
  exact (F.realAdaptedPolynomialTensor_coordinates w b ω hF _ z).trans
    (F.reducedNativeSection_real_coordinate_zero b ω hF w g.coord z hz)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealReducedCoefficientMap
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def realReducedSquareCoefficientMap (w : σ → ℕ) :
    (ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w) →ₗ[ℝ]
      F.RealFirstCoefficientModule w :=
  (F.firstCoefficientRealEquiv w).toLinearMap.comp
    ((F.reducedSquareCoefficientMap w).baseChange ℝ)

theorem realReducedSquareCoefficientMap_relative (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realReducedSquareCoefficientMap w (F.realReducedRelativeSquareSymbolMap w hw x) =
      F.realNormalizedFirstCoefficientMap w x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    change F.firstCoefficientRealEquiv w
      (r ⊗ₜ[ℚ] F.reducedSquareCoefficientMap w (F.reducedRelativeSquareSymbolMap w hw x)) =
      F.firstCoefficientRealEquiv w (r ⊗ₜ[ℚ] F.normalizedFirstCoefficientMap w x)
    rw [F.reducedSquareCoefficientMap_relative]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedDiagonalBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

variable (w : σ → ℕ)
  [Fintype (QuotientTopSymbolIndex s w ω)]

theorem reducedSquareRealDiagonalHom_coord
    (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareRealDiagonalHom w g).coord =
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ g.coord := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledCurrentLayerPolynomialStep
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct Matrix

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_current_layer_polynomial_step
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    (hgraded : BasisHomogeneousBrackets (b.baseChange ℝ) w)
    {j H J l : ℕ} (hj : 0 < j)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : ((l * j : ℕ) : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P Pj : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPU : ∀ α, coefficients P α ∈ U)
    (hPgraded : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPj : Pj = map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P)
    (hPjE : ∀ α, coefficients Pj α ∈ E.baseChange ℝ)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients (S i) α = 0)
    (hR : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients (R i) α = 0)
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) Pj - S i - R i) α ∈ V.baseChange ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbudget : (Fintype.card σ : ℝ) / j * M ≤ Real.exp p)
    (hslow : ∀ i α n, |realQuotientCoordinateMap f (coefficients (S i) α) n| ≤
      M / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈ realDenominatorGrid l) :
    ∃ (m : ℕ) (A B P' : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      P' = bchRemove s A P B ∧ lieBCH s (lieBCH s A P') B = P ∧
      coefficients P' 0 = coefficients P 0 ∧
      P' ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
      (∀ α, coefficients P' α ∈ U) ∧
      (∀ α, coefficients (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P') α ∈
        (E ⊓ V).baseChange ℝ) ∧
      ∀ d < j, map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P' =
        map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P := by
  have hPjhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients Pj α = 0 := by
    intro α hα
    rw [hPj]
    exact gradedPolynomialSubmodule_projection_homogeneous (b.baseChange ℝ) w (fun _ => 1)
      P hPgraded j α hα
  have h := exists_homogeneous_subspace_corrections_from_derivatives b e f hH hl hj
    hA he hp hrows hcols hHp hlp T hT Pj hPjE hPjhom S R hS hR hsplit hM hbudget hslow hrational
  obtain ⟨m, A, B, hm, hmp, _, _, hAB, hAhom, hBhom, hAnorm, hBgrid, hres⟩ := h
  have hA0 : coefficients A 0 = 0 := hAhom 0 (by simpa using Nat.ne_of_lt hj)
  have hB0 : coefficients B 0 = 0 := hBhom 0 (by simpa using Nat.ne_of_lt hj)
  have hgrades := F.polynomial_bchRemove_grades b w hlayers (E.baseChange ℝ) j hE A P B
    (fun α => (hAB α).1) (fun α => (hAB α).2)
  have hAgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    j A hAhom (fun α => hE _ (hAB α).1)
  have hBgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    j B hBhom (fun α => hE _ (hAB α).2)
  refine ⟨m, A, B, bchRemove s A P B, hm, hmp, hAB, hAhom, hBhom, hAnorm, hBgrid, rfl,
    bchRemove_factorization F.realification.lowerCentralSeries_eq_bot A P B,
    bchRemove_constant F.realification.lowerCentralSeries_eq_bot A P B hA0 hB0,
    bchRemove_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w hgraded (fun _ => 1) s A P B
      hAgraded hPgraded hBgraded,
    bchRemove_coefficients_mem U s A P B (fun α => hEU _ (hAB α).1) hPU
      (fun α => hEU _ (hAB α).2), ?_, hgrades.2⟩
  intro α
  rw [hgrades.1, ← hPj]
  exact hres α

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFormalCurrentLayerStep
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem homogeneous_pderiv_coordinate_bound [Fintype σ] [Fintype ι]
    (q : L →ₗ[ℚ] (ι → ℝ)) (P : VectorPolynomial σ ℚ L) (j : ℕ)
    (hP : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients P α = 0)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ α, ‖q (coefficients P α)‖ ≤ M / monomialScale T α)
    (i : σ) (α : σ →₀ ℕ) :
    ‖q (coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L P) α)‖ ≤
      j * M / (T i * monomialScale T α) := by
  classical
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg j) hM)
    (mul_pos (hT i) (monomialScale_pos T hT α)).le)).mpr
  intro n
  let f := (LinearMap.proj n).comp q
  have hdegree : ∀ (β : σ →₀ ℕ) k, j < β k → f (coefficients P β) = 0 := by
    intro β k hk
    have hw := Finsupp.le_weight (fun _ : σ => (1 : ℕ)) (s := k) (by decide) β
    have hne : Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ j := by omega
    rw [hP β hne, map_zero]
  have hcoord (β : σ →₀ ℕ) : |f (coefficients P β)| ≤ M / monomialScale T β := by
    exact (norm_le_pi_norm (q (coefficients P β)) n).trans (hbound β)
  have h := directionalDerivative_single_scaled_bound f P j hdegree T hT M hM hcoord i α
  rw [directionalDerivative_single] at h
  change |f (coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L P) α)| ≤ _
  convert h using 1
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ ι σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype σ] [Fintype ι] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem current_correction_derivative_terms_vanish (hs : 2 ≤ s)
    (V : Submodule ℚ L) (f : Basis ι ℚ (L ⧸ V)) {j l m : ℕ} (hj : 0 < j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
        (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V.baseChange ℝ)
    (hnew : ∀ α, coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (A⁻¹ * P * B⁻¹).coord) α ∈ V.baseChange ℝ)
    {p M C : ℝ} (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hdim : (Fintype.card ι : ℝ) ≤ p) (hl : 0 < l) (hm : 0 < m)
    (hden : ((l * m : ℕ) : ℝ) ≤ Real.exp p) (hsize : M + j * C ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (hsmall : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l)
    (hAnorm : ∀ α, ‖realQuotientCoordinateMap f (coefficients A.coord α)‖ ≤ C / monomialScale T α)
    (hBgrid : ∀ α, realQuotientCoordinateMap f (coefficients B.coord α) ∈ realDenominatorGrid m) :
    ∀ i α, coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint A⁻¹ (small i - formalLogDerivative i A))) α ∈ V.baseChange ℝ ∧
      coefficients (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint B (rational i) - formalLogDerivative i B)) α ∈ V.baseChange ℝ := by
  let π := VectorPolynomial.map (σ := σ) ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
  let q := (realQuotientCoordinateMap f).restrictScalars ℚ
  let small' := fun i => π (dualAdjoint A⁻¹ (small i - formalLogDerivative i A))
  let rational' := fun i => π (dualAdjoint B (rational i) - formalLogDerivative i B)
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hparts (i : σ) := F.current_derivative_removal_projection b w hlayers hs hj i A B hA hB (small i) (rational i)
  have hsmall' : ∀ i α, ‖realQuotientCoordinateMap f (coefficients (small' i) α)‖ ≤
      Real.exp p / (T i * monomialScale T α) := by
    intro i α
    have hD := homogeneous_pderiv_coordinate_bound q A.coord j hAhom T hTpos hC hAnorm i α
    have he : small' i = π (small i) - (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord :=
      (hparts i).1
    rw [he, map_sub, Finsupp.sub_apply, map_sub]
    calc
      _ ≤ ‖realQuotientCoordinateMap f (coefficients (π (small i)) α)‖ +
          ‖realQuotientCoordinateMap f (coefficients
            ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord) α)‖ := norm_sub_le _ _
      _ ≤ M / (T i * monomialScale T α) + j * C / (T i * monomialScale T α) := add_le_add (hsmall i α) hD
      _ = (M + j * C) / (T i * monomialScale T α) := by ring
      _ ≤ Real.exp p / (T i * monomialScale T α) :=
        div_le_div_of_nonneg_right hsize (mul_pos (hTpos i) (monomialScale_pos T hTpos α)).le
  have hrational' : ∀ i α, realQuotientCoordinateMap f (coefficients (rational' i) α) ∈
      realDenominatorGrid (l * m) := by
    intro i α
    have he : rational' i = π (rational i) - (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) B.coord :=
      (hparts i).2
    rw [he, map_sub, Finsupp.sub_apply, map_sub]
    exact realDenominatorGrid_sub_product l m _ _ (hrational i α)
      (pderiv_coordinate_grid q B.coord m hBgrid i α)
  apply current_derivative_terms_vanish_of_invariant_polynomial V f (Nat.mul_pos hl hm) hp hdim hden T hT
    (π (A⁻¹ * P * B⁻¹).coord) hnew small' rational' hsmall' hrational'
  intro i α
  have he := F.current_derivative_defect_preserved b w hlayers hs hj i P A B hA hB (small i) (rational i)
  change coefficients
    ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (π (A⁻¹ * P * B⁻¹).coord) - small' i - rational' i) α ∈ _
  rw [he]
  exact hsplit i α

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_formal_current_layer_step
    (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {j H J Q l : ℕ} (hj : 2 ≤ j)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p q M : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hrows : (Fintype.card ι : ℝ) ≤ p) (hcols : (Fintype.card ν : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : ((l * j : ℕ) : ℝ) ≤ Real.exp p)
    (hbudget : (Fintype.card σ : ℝ) / j * M ≤ Real.exp p)
    (hrowsq : (Fintype.card ι : ℝ) ≤ q)
    (hden : ((l * matrixDenominator (quotientCoordinateMatrix b f) *
        matrixDenominator (bracketLiftMatrix b e) : ℕ) : ℝ) * Real.exp ((p + 2) ^ 36) ≤ Real.exp q)
    (hsize : M + j * ((((Fintype.card μ : ℝ) + 1) * (Q + 1)) *
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p)) ≤ Real.exp q)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (hTq : ∀ i, Real.exp (separationBudget q) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P.coord α) ∈ E.baseChange ℝ)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ)
    (hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (hSgraded : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hRgraded : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hslow : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (hgrid : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l) :
    ∃ (m : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, coefficients (VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) α ∈ (E ⊓ V).baseChange ℝ) ∧
        (∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i, small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        (∀ i α, coefficients (small' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (rational' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K) ∧
        (∀ α d, 2 ≤ d → d < j + 1 →
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V.baseChange ℝ) ∧
        (∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
          V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        ∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  let π := VectorPolynomial.map (σ := σ) ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
  have hjpos : 0 < j := by omega
  have hsplit := F.formal_current_layer_derivative_equation_mod b w hlayers hs U (V.baseChange ℝ) K
    hUV hV hj P hPU hK hlower hbracket small rational extra hrational hextra hsystem
  have h := F.exists_controlled_current_layer_polynomial_step b w hlayers Uq e f (hgraded.baseChange b w)
    hjpos hE hEU hH hl hA he hp hrows hcols hHp hlp T hT P.coord (π P.coord) hPU hPgraded rfl
    (fun α => by rw [coefficients_map]; exact hPE α) (fun i => π (small i)) (fun i => π (rational i))
    (fun i => shifted_one_projection_homogeneous (b.baseChange ℝ) w _ (hSgraded i) hjpos)
    (fun i => shifted_one_projection_homogeneous (b.baseChange ℝ) w _ (hRgraded i) hjpos)
    hsplit hM hbudget
    (fun i α n => (norm_le_pi_norm (realQuotientCoordinateMap f (coefficients (π (small i)) α)) n).trans (hslow i α)) hgrid
  obtain ⟨m, a, c, Pnew, hm, hmp, hac, hahom, hchom, hanorm, hcgrid,
    hremove, _, hconstant, hnewgraded, hnewU, hnewV, hbelow⟩ := h
  let A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot := ⟨a⟩
  let B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot := ⟨c⟩
  let P' := A⁻¹ * P * B⁻¹
  have hcoord : P'.coord = Pnew := hremove.symm
  have hApure : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α :=
    fun α => hE _ (hac α).1
  have hBpure : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α :=
    fun α => hE _ (hac α).2
  have hAU : ∀ α, coefficients A.coord α ∈ Uq := fun α => hEU _ (hac α).1
  have hBU : ∀ α, coefficients B.coord α ∈ Uq := fun α => hEU _ (hac α).2
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hApure α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hBlayer : ∀ α, coefficients B.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hBpure α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  let C : ℝ := (((Fintype.card μ : ℝ) + 1) * (Q + 1)) *
    (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAnorm : ∀ α, ‖realQuotientCoordinateMap f (coefficients A.coord α)‖ ≤ C / monomialScale T α := by
    intro α
    calc
      _ ≤ (((Fintype.card μ : ℝ) + 1) * (Q + 1)) * ‖(b.baseChange ℝ).equivFun (coefficients a α)‖ :=
        realQuotientCoordinateMap_norm_bound b f hf _
      _ ≤ (((Fintype.card μ : ℝ) + 1) * (Q + 1)) *
          ((((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
        mul_le_mul_of_nonneg_left (hanorm α) (by positivity)
      _ = C / monomialScale T α := by dsimp [C]; ring
  let n := matrixDenominator (quotientCoordinateMatrix b f) * (matrixDenominator (bracketLiftMatrix b e) * m)
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos _) (Nat.mul_pos (matrixDenominator_pos _) hm)
  have hBgrid : ∀ α, realQuotientCoordinateMap f (coefficients B.coord α) ∈ realDenominatorGrid n :=
    fun α => realQuotientCoordinateMap_grid b f _ _ (hcgrid α)
  have hden' : ((l * n : ℕ) : ℝ) ≤ Real.exp q := by
    calc
      _ = ((l * matrixDenominator (quotientCoordinateMatrix b f) *
          matrixDenominator (bracketLiftMatrix b e) : ℕ) : ℝ) * (m : ℝ) := by
        dsimp [n]
        push_cast
        ring
      _ ≤ ((l * matrixDenominator (quotientCoordinateMatrix b f) *
          matrixDenominator (bracketLiftMatrix b e) : ℕ) : ℝ) * Real.exp ((p + 2) ^ 36) :=
        mul_le_mul_of_nonneg_left hmp (by positivity)
      _ ≤ Real.exp q := hden
  have hnew : ∀ α, coefficients (π P'.coord) α ∈ V.baseChange ℝ := by
    intro α
    rw [hcoord]
    exact Submodule.baseChange_mono ℝ inf_le_right (hnewV α)
  have hvanish := F.current_correction_derivative_terms_vanish b w hlayers hs V f hjpos P A B
    hApure hBpure hahom small rational hsplit hnew hq hC hrowsq hl hn hden' hsize T hTq hslow hgrid hAnorm hBgrid
  have hadvance := F.formal_current_derivative_advance b w hlayers Uq (V.baseChange ℝ) hUV hV j A B
    hAU hBU hAlayer hBlayer small rational hsmall hrational hvanish
  have hAgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j a hahom hApure
  have hBgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j c hchom hBpure
  have hlog := F.formal_correction_advances_log_conditions b w hlayers hj (V.baseChange ℝ) K
    P A B hAlayer hBlayer hK hlower hnew
  have hWiff (x : ℝ ⊗[ℚ] L) :
      x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔ F.realification.layer (j + 1) ↔
        x ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
    change x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔
      (F.realLayer (j + 1)).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hbracket' : ∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
      V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
    intro α k hk
    exact (hWiff _).mp (F.realification.formal_correction_preserves_bracket_remainder
      ((V.baseChange ℝ).restrictScalars ℚ) j P A B hAlayer hBlayer k
      (fun β => (hWiff _).mpr (hbracket β k hk)) α)
  refine ⟨m, A, B, hm, hmp, hac, hahom, hchom, hanorm, hcgrid, ?_, ?_, ?_, ?_, ?_, ?_,
    PolynomialDerivativeSystemMod.remove Uq ((V.baseChange ℝ).restrictScalars ℚ) hUV P A B hAU
      small rational extra hsystem, ?_, hadvance, hlog.1, hlog.2, hbracket',
    F.formal_correction_preserves_horizontal_extra b w hlayers hs hj (V.baseChange ℝ)
      P A B hAlayer hBlayer extra hextra⟩
  · group
  · change coefficients P'.coord 0 = _
    rw [hcoord]
    exact hconstant
  · change P'.coord ∈ _
    rw [hcoord]
    exact hnewgraded
  · intro α
    change coefficients P'.coord α ∈ _
    rw [hcoord]
    exact hnewU α
  · intro α
    change coefficients (π P'.coord) α ∈ _
    rw [hcoord]
    exact hnewV α
  · intro d hd
    change VectorPolynomial.map _ P'.coord = _
    rw [hcoord]
    exact hbelow d hd
  · intro i
    exact polynomial_derivative_removal_preserves_shifted_grading (b.baseChange ℝ) w (hgraded.baseChange b w)
      i A B (small i) (rational i) hAgraded hBgraded (hSgraded i) (hRgraded i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_current_layer_step :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p M : ℝ} (_hp : 0 ≤ p) (_hM : 0 ≤ M)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hrows : (Fintype.card ι : ℝ) ≤ p)
    (_hcols : (Fintype.card ν : ℝ) ≤ p) (_hvariables : (Fintype.card σ : ℝ) ≤ p)
    (_hjp : (j : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p) (_hMp : M ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P.coord α) ∈ E.baseChange ℝ)
    (_hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (_hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ)
    (_hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hsmall : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hrational : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (_hSgraded : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hslow : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (_hgrid : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, coefficients (VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) α ∈ (E ⊓ V).baseChange ℝ) ∧
        (∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i, small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        (∀ i α, coefficients (small' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (rational' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K) ∧
        (∀ α d, 2 ≤ d → d < j + 1 →
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V.baseChange ℝ) ∧
        (∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
          V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        ∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  obtain ⟨C, hC, hCbound⟩ := exists_current_layer_uniform_budget
  refine ⟨C, hC, ?_⟩
  intro L μ ι ν σ _ _ _ _ _ _ s F b w hlayers E V
    hgraded hs U K hUV hV e f j H J Q l hj hE hEU hH hl hA he hf
    p M hp hM hambient hrows hcols hvariables hjp hHp hJp hQp hlp hMp T hT
    P hPU hPgraded hPE hK hlower hbracket small rational extra hsmall hrational hextra
    hsystem hSgraded hRgraded hslow hgrid
  let t := currentLayerConstructionBudget p
  let q := currentLayerRemovalBudget p
  have ht : 0 ≤ t := currentLayerConstructionBudget_nonneg hp
  have hq : 0 ≤ q := currentLayerRemovalBudget_nonneg hp
  have hpt : p ≤ t := le_currentLayerConstructionBudget hp
  have hEt : Real.exp p ≤ Real.exp t := Real.exp_le_exp.mpr hpt
  have hconstruction := current_layer_construction_budget_bounds hM (Fintype.card σ) j l
    hvariables (by omega) hjp hlp hMp
  have hpplus : Real.exp p ≤ Real.exp ((p + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  have hD := matrixDenominator_le_exp_power (quotientCoordinateMatrix b f) hp 1 hrows hambient (fun i n => by
    have hden : (((quotientCoordinateMatrix b f i n).den) : ℝ) ≤ Q := Nat.cast_le.mpr (hf i n).2
    exact (hden.trans hQp).trans hpplus)
  have hEden := matrixDenominator_le_exp_power (bracketLiftMatrix b e) hp 1 hambient hcols (fun i n => by
    have hden : (((bracketLiftMatrix b e i n).den) : ℝ) ≤ J := Nat.cast_le.mpr (he i n).2
    exact (hden.trans hJp).trans hpplus)
  obtain ⟨hpq, hden, hsize, _, haCap, hbCap⟩ := current_layer_removal_budget_bounds hp
    (Fintype.card μ) (Fintype.card ν) j J Q l
    (matrixDenominator (quotientCoordinateMatrix b f)) (matrixDenominator (bracketLiftMatrix b e))
    hambient hcols hjp hJp hQp hlp hMp hD hEden
  have hCval : separationBudget t + separationBudget q + q ≤ (p + C) ^ C := hCbound p hp
  have hst := separationBudget_nonneg ht
  have hsq := separationBudget_nonneg hq
  have htCut : separationBudget t ≤ (p + C) ^ C := by linarith
  have hqCut : separationBudget q ≤ (p + C) ^ C := by linarith
  have hqBound : q ≤ (p + C) ^ C := by linarith
  have hTt : ∀ i, Real.exp (separationBudget t) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr htCut).trans (hT i)
  have hTq : ∀ i, Real.exp (separationBudget q) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hqCut).trans (hT i)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hstep := F.exists_controlled_formal_current_layer_step b w hlayers (p := t) (q := q)
    hgraded hs U K hUV hV e f hj hE hEU hH hl hA he hf ht hq hM
    (hrows.trans hpt) (hcols.trans hpt) (hHp.trans hEt) hconstruction.1 hconstruction.2
    (hrows.trans hpq) hden hsize T hTt hTq P hPU hPgraded hPE hK hlower hbracket
    small rational extra hsmall hrational hextra hsystem hSgraded hRgraded hslow hgrid
  obtain ⟨m, A, B, hm, hmp, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra⟩ := hstep
  let n := matrixDenominator (bracketLiftMatrix b e) * m
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos _) hm
  have hnbound : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (matrixDenominator (bracketLiftMatrix b e) : ℝ) * (m : ℝ) := by dsimp [n]; rw [Nat.cast_mul]
      _ ≤ (matrixDenominator (bracketLiftMatrix b e) : ℝ) * Real.exp ((t + 2) ^ 36) :=
        mul_le_mul_of_nonneg_left hmp (Nat.cast_nonneg _)
      _ ≤ Real.exp q := hbCap
      _ ≤ _ := Real.exp_le_exp.mpr hqBound
  refine ⟨n, A, B, hn, hnbound, hAB, hAhom, hBhom, ?_, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra⟩
  intro α
  exact (hAnorm α).trans (div_le_div_of_nonneg_right
    (haCap.trans (Real.exp_le_exp.mpr hqBound)) (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.StepDropBasisBudget
namespace OAI

section

namespace Erdos3

open Module

theorem exists_stepDrop_basis_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype κ] [Fintype ν]
    (b : Basis μ ℚ L) (w : μ → ℕ) (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H : ℕ} (_hH : 1 ≤ H)
    (_hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (_hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (_hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (_heK : ∀ i j, RationalHeightLE (b.repr (eK j : L) i) H)
    (_hstructure : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hυ : (Fintype.card υ : ℝ) ≤ p)
    (_hχ : (Fintype.card χ : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hν : (Fintype.card ν : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p),
    ∃ e : Basis (Fin (Module.finrank ℚ (stepDropSubmodule b w U V K)))
      ℚ (stepDropSubmodule b w U V K), ∀ i j,
      (((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
      (((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + 2) ^ 5 + 2) ^ 9)
  refine ⟨C, hC, ?_⟩
  intro L μ υ χ κ ν _ _ _ _ _ _ _ b w U V K fU fK fV eK H hH hU hK hV heK hstructure
    p hp hμ hυ hχ hκ hν hHp
  let q := (p + 2) ^ 5
  let J := max H (stepDropBracketHeight (Fintype.card μ) H)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have hp2 : p ≤ p + 2 := by linarith
    apply hp2.trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 1 ≤ 5)
  have hrows : (Fintype.card (StepDropRow υ χ κ ν) : ℝ) ≤ q := by
    simp only [StepDropRow, Fintype.card_sum, Fintype.card_prod, Nat.cast_add, Nat.cast_mul]
    have hprod : (Fintype.card κ : ℝ) * Fintype.card ν ≤ p * p :=
      mul_le_mul hκ hν (Nat.cast_nonneg _) hp
    have hpoly : p ^ 2 + 3 * p ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 10 * p ^ 4 + 40 * p ^ 3 + 79 * p ^ 2 + 77 * p + 32 := by positivity
      nlinarith
    dsimp [q]
    nlinarith
  have hJ : 1 ≤ J := hH.trans (Nat.le_max_left _ _)
  have hJq : (J : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_max]
    exact max_le (hHp.trans (Real.exp_le_exp.mpr hpq))
      (stepDropBracketHeight_le_exp (Fintype.card μ) H hp hμ hHp)
  obtain ⟨e, he⟩ := exists_stepDrop_basis_exp_height b w U V K fU fK fV eK hJ
    (fun i j => (hU i j).mono (Nat.le_max_left _ _))
    (fun i j => (hK i j).mono (Nat.le_max_left _ _))
    (fun i j => (hV i j).mono (Nat.le_max_left _ _))
    (fun i j z => (stepDrop_bracket_height b V K fV eK hV heK hstructure i j z).mono (Nat.le_max_right _ _))
    hq (hμ.trans hpq) hrows hJq
  have hcap : (q + 2) ^ 9 ≤ (p + C) ^ C := by
    simpa [q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨e, fun i j => ⟨(he i j).1.trans (Real.exp_le_exp.mpr hcap),
    (he i j).2.trans (Real.exp_le_exp.mpr hcap)⟩⟩

end Erdos3

end

end OAI
end


