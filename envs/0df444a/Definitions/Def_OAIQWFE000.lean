-- Prove2me | Definitions.Def_OAIQWFE000
-- name    : OAIQWFE000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T01:07:30.660366+00:00
-- url     : https://prove2.me/theorems/c156a518-af2e-402e-ba0b-70bd51740c86
-- title:
--   OpenAI finite-entropy separation split: definitions bundle 1 (Fock spaces, free tensor model, Gaussian and matrix tools)
-- statement:
--   The first definitions bundle of the split of OpenAI's proof that Voiculescu's microstates and nonmicrostates free entropies differ for a bounded self-adjoint tuple with finite entropy (`OAI.FiniteEntropySeparation.main`). It holds OpenAI's Lean definitions from `lean/OAI/Analysis/FreeEntropy` (OpenAI, *A finite-entropy separation of microstates and nonmicrostates free entropy*, OpenAI Math Release, September 25, 2026, result family 298, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies.
--
--   Among them: the full Fock space and its creation and semicircular operators (module `Basic`), the free tensor model `FreeTensor.Space`, `FreeTensor.algebra`, `FreeTensor.tracialVector`, `FreeTensor.semicircularN`, `FreeTensor.backgroundAlgebra` (modules `TracialRealization`, `HeatTensor`), the product Gaussian measure `productGaussian`, Gaussian smoothing `smoothedDensity`, the Fisher test functions `fisherTest` and `WordPolynomial`, the matrix coordinates and block events (`blockEvent`, `diagonalMicrostates`), the concrete model `Model.H`, `Model.M`, `Model.τ`, `Model.X`, `Model.auxiliaryNoise`, `Model.fisherDeficit`, `Model.cumulantConstant`, `Model.gaussianEntropy`, `Model.heatFisherReal`, the equidistant atoms `equidiscreteAtom`, and the constants `chosenP` $= 2^{64}$, `chosenTime` $= 2^{48}$, `chosenStart`.
--
--   The definitions of the published statement (`TracialVector`, `trace`, `wordEval`, `wordMoment`, `FreeSubalgebras`, `FreeStandardNoise`, `polynomialL2`, `derivativeMoment`, `ConjugateSystem`, `freeFisher`, `heatTuple`, `chiStar`, `MatrixCoordinates`, `hermitianMatrix`, `matrixOpNorm`, `matrixMoment`, `microstates`, `chiCutoff`, `chi`) are not repeated: the bundle imports them from the published bundle `Def_FiniteEntropySeparation`. It imports no other bundle.
--
--   Modules: `Basic`, `GaussianHermite`, `TensorHermite`, `GaussianKernel`, `GaussianDifferential`, `GaussianConvolution`, `CoordinateMask`, `MatrixChart`, `MatrixBasis`, `TensorPoincare`, `PolynomialFunctions`, `ComplexPolynomialFunctions`, `MatrixPolynomial`, `MatrixWordDerivative`, `FisherVariational`, `TracialRealization`, `HeatTensor`, `MatrixChartInverse`, `MatrixHilbertSchmidt`, `SpectralBlockMask`, `BlockEvent`, `MicrostatesSelection`, `GaussianLinearTail`, `GUEOperatorTail`, `GUEDerivative`, `GUEMoments`, `GUELimit`, `WordSeries`, `CumulantSeries`, `SeriesNorm`, `VectorSeries`, `SeriesWeights`, `SeriesAnalytic`, `SemicircularSeries`, `CyclicSeries`, `LinearSeries`, `EmbeddedSeries`, `Signal`, `TensorLaw`, `NoiseTensor`, `TensorConcat`, `TensorFreeness`, `EquidiscreteSignal`, `ActualTuple`, `MixedGaussianSeries`, `HeatCumulants`, `MatrixReparam`, `GUEFreeLaw`, `GUESelection`, `MicrostatesHeat`, `SpectralClustering`, `SpectralTestFunctions`, `SpectralParameters`, `OptionSeries`, `SignalSeries`, `MonomialSeries`, `WickSeries`, `CumulantResidual`, `TwoNoiseFisher`, `SignalCovariance`, `SeriesSummability`, `WickCoefficients`, `GeometricTail`, `FisherDeficit`, `BlockGaussianQuantitative`, `GaussianDeBruijn`, `GaussianEntropyEvent`, `HeatAnalysis`, `EntropyReal`, `FlowSeparation`, `MatrixBlocks` (each `.lean` in `lean/OAI/Analysis/FreeEntropy`).
-- source:
--   OpenAI, A finite-entropy separation of microstates and nonmicrostates free entropy, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 298; Apache License 2.0); definitions carved from lean/OAI/Analysis/FreeEntropy at commit adc7f12

import Mathlib
import Definitions.Def_FiniteEntropySeparation

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter

namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] theorem trace_zero {M : VonNeumannAlgebra H} (τ : TracialVector M) :
    trace τ (0 : H →L[ℂ] H) = 0 := by simp [trace]

@[simp] theorem trace_one {M : VonNeumannAlgebra H} (τ : TracialVector M) :
    trace τ (1 : H →L[ℂ] H) = 1 := by
  simp [trace, inner_self_eq_norm_sq_to_K, τ.norm_vacuum]

@[simp] theorem wordMoment_nil {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) : wordMoment τ X [] = 1 := by
  simp [wordMoment, wordEval]

def commutatorKernel {n : ℕ} (P : H →L[ℂ] H) (X : Fin n → H →L[ℂ] H)
    (i : Fin n) (w : List (Fin n)) : H →L[ℂ] H :=
  ∑ r : Fin w.length, if w[r.val] = i then
    wordEval X (w.take r.val) * P * wordEval X (w.drop (r.val + 1)) else 0

omit [CompleteSpace H] in
@[simp] theorem commutatorKernel_nil {n : ℕ} (P : H →L[ℂ] H)
    (X : Fin n → H →L[ℂ] H) (i : Fin n) : commutatorKernel P X i [] = 0 := by
  simp [commutatorKernel]

namespace Fock

open scoped lp
variable {ι : Type} [DecidableEq ι]

abbrev Space (ι : Type) := lp (fun _ : List ι => ℂ) 2

instance space_nontrivial : Nontrivial (Space ι) := by
  refine ⟨⟨lp.single 2 ([] : List ι) (1 : ℂ), 0, ?_⟩⟩
  intro h
  have he := congrArg (fun f : Space ι => f []) h
  simp at he

def basisVector (w : List ι) : Space ι := lp.single 2 w 1

def coordinateIsometry (w : List ι) : ℂ →ₗᵢ[ℂ] Space ι where
  toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : List ι => ℂ) 2 w
  norm_map' z := lp.norm_single (E := fun _ : List ι => ℂ) (p := 2) (by norm_num) w z

@[simp] theorem coordinateIsometry_apply (w : List ι) (z : ℂ) :
    coordinateIsometry w z = lp.single 2 w z := rfl

theorem orthogonal_coordinates (f : List ι → List ι) (hf : Function.Injective f) :
    OrthogonalFamily ℂ (fun _ : List ι => ℂ) (fun w => coordinateIsometry (f w)) := by
  intro w v hwv a b
  simp only [coordinateIsometry_apply, lp.inner_single_left]
  rw [lp.single_apply_ne (E := fun _ : List ι => ℂ) 2 (f v) b (fun h => hwv (hf h))]
  simp

def injectionIsometry (f : List ι → List ι) (hf : Function.Injective f) :
    Space ι →ₗᵢ[ℂ] Space ι :=
  (orthogonal_coordinates f hf).linearIsometry

@[simp] theorem injectionIsometry_single (f : List ι → List ι)
    (hf : Function.Injective f) (w : List ι) (z : ℂ) :
    injectionIsometry f hf (lp.single 2 w z) = lp.single 2 (f w) z := by
  exact (orthogonal_coordinates f hf).linearIsometry_apply_single z

def creation (i : ι) : Space ι →L[ℂ] Space ι :=
  (injectionIsometry (List.cons i) (List.cons_injective (a := i))).toContinuousLinearMap

def rightCreation (i : ι) : Space ι →L[ℂ] Space ι :=
  (injectionIsometry (fun w => w ++ [i]) (List.append_left_injective [i])).toContinuousLinearMap

@[simp] theorem creation_single (i : ι) (w : List ι) (z : ℂ) :
    creation i (lp.single 2 w z) = lp.single 2 (i :: w) z := by
  exact injectionIsometry_single (List.cons i) List.cons_injective w z

@[simp] theorem rightCreation_single (i : ι) (w : List ι) (z : ℂ) :
    rightCreation i (lp.single 2 w z) = lp.single 2 (w ++ [i]) z := by
  exact injectionIsometry_single (fun w => w ++ [i]) (List.append_left_injective [i]) w z

def semicircular (i : ι) : Space ι →L[ℂ] Space ι := creation i + star (creation i)

def rightSemicircular (i : ι) : Space ι →L[ℂ] Space ι :=
  rightCreation i + star (rightCreation i)

theorem semicircular_selfAdjoint (i : ι) : IsSelfAdjoint (semicircular i) :=
  IsSelfAdjoint.add_star_self (creation i)

theorem rightSemicircular_selfAdjoint (i : ι) : IsSelfAdjoint (rightSemicircular i) :=
  IsSelfAdjoint.add_star_self (rightCreation i)

@[simp] theorem adjoint_creation_apply (i : ι) (x : Space ι) (w : List ι) :
    (star (creation i) x) w = x (i :: w) := by
  have h := ContinuousLinearMap.adjoint_inner_right (creation i) (lp.single 2 w (1 : ℂ)) x
  simpa [ContinuousLinearMap.star_eq_adjoint, lp.inner_single_left] using h

@[simp] theorem adjoint_rightCreation_apply (i : ι) (x : Space ι) (w : List ι) :
    (star (rightCreation i) x) w = x (w ++ [i]) := by
  have h := ContinuousLinearMap.adjoint_inner_right (rightCreation i) (lp.single 2 w (1 : ℂ)) x
  simpa [ContinuousLinearMap.star_eq_adjoint, lp.inner_single_left] using h

@[simp] theorem annihilation_single_nil (i : ι) (z : ℂ) :
    star (creation i) (lp.single 2 ([] : List ι) z) = 0 := by
  apply lp.ext
  funext w
  simp [lp.single_apply]

@[simp] theorem annihilation_single_cons (i j : ι) (w : List ι) (z : ℂ) :
    star (creation i) (lp.single 2 (j :: w) z) =
      if i = j then lp.single 2 w z else 0 := by
  apply lp.ext
  funext v
  by_cases h : i = j
  · subst j
    simp [lp.single_apply, Pi.single_apply]
  · simp [lp.single_apply, h]

@[simp] theorem rightAnnihilation_single_nil (i : ι) (z : ℂ) :
    star (rightCreation i) (lp.single 2 ([] : List ι) z) = 0 := by
  apply lp.ext
  funext w
  simp [lp.single_apply]

@[simp] theorem rightAnnihilation_single_append (i j : ι) (w : List ι) (z : ℂ) :
    star (rightCreation i) (lp.single 2 (w ++ [j]) z) =
      if i = j then lp.single 2 w z else 0 := by
  apply lp.ext
  funext v
  by_cases h : i = j
  · subst j
    simp [lp.single_apply, Pi.single_apply]
  · simp [lp.single_apply, h]

@[simp] theorem semicircular_single_nil (i : ι) (z : ℂ) :
    semicircular i (lp.single 2 ([] : List ι) z) = lp.single 2 [i] z := by
  simp [semicircular]

@[simp] theorem semicircular_single_cons (i j : ι) (w : List ι) (z : ℂ) :
    semicircular i (lp.single 2 (j :: w) z) =
      lp.single 2 (i :: j :: w) z + if i = j then lp.single 2 w z else 0 := by
  simp [semicircular]

@[simp] theorem rightSemicircular_single_nil (i : ι) (z : ℂ) :
    rightSemicircular i (lp.single 2 ([] : List ι) z) = lp.single 2 [i] z := by
  simp [rightSemicircular]

@[simp] theorem rightSemicircular_single_append (i j : ι) (w : List ι) (z : ℂ) :
    rightSemicircular i (lp.single 2 (w ++ [j]) z) =
      lp.single 2 (w ++ [j, i]) z + if i = j then lp.single 2 w z else 0 := by
  simp [rightSemicircular]

theorem semicircular_commutes_right (i j : ι) :
    Commute (semicircular i) (rightSemicircular j) := by
  show semicircular i * rightSemicircular j = rightSemicircular j * semicircular i
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change semicircular i (rightSemicircular j (lp.single 2 w z)) =
    rightSemicircular j (semicircular i (lp.single 2 w z))
  cases w with
  | nil =>
    simp only [rightSemicircular_single_nil, semicircular_single_nil,
      semicircular_single_cons]
    rw [show [i] = [] ++ [i] from rfl, rightSemicircular_single_append]
    by_cases h : i = j <;> simp [h, eq_comm]
  | cons k v =>
    induction v using List.reverseRecOn with
    | nil =>
      rw [show [k] = [] ++ [k] from rfl, rightSemicircular_single_append]
      simp only [List.nil_append, map_add, semicircular_single_cons]
      rw [show [i, k] = [i] ++ [k] from rfl, rightSemicircular_single_append]
      by_cases hik : i = k <;> by_cases hjk : j = k <;>
        simp [hik, hjk, rightSemicircular_single_nil]
    | append_singleton v l _ =>
      rw [show k :: (v ++ [l]) = (k :: v) ++ [l] from rfl,
        rightSemicircular_single_append]
      simp only [map_add, List.cons_append, semicircular_single_cons]
      rw [show i :: k :: (v ++ [l]) = (i :: k :: v) ++ [l] from rfl,
        rightSemicircular_single_append]
      by_cases hik : i = k <;> by_cases hjl : j = l <;>
        simp [hik, hjl, rightSemicircular_single_append, add_assoc, add_comm, add_left_comm]

def rightWick : List ι → Space ι →L[ℂ] Space ι
  | [] => 1
  | [i] => rightSemicircular i
  | i :: j :: w => rightSemicircular i * rightWick (j :: w) -
      if i = j then rightWick w else 0

 theorem commute_rightWick (A : Space ι →L[ℂ] Space ι)
    (h : ∀ i, Commute A (rightSemicircular i)) (w : List ι) :
    Commute A (rightWick w) := by
  induction w using rightWick.induct with
  | case1 => exact Commute.one_right A
  | case2 i => exact h i
  | case3 i j w ih₁ ih₂ =>
    dsimp only [rightWick]
    apply ((h i).mul_right ih₁).sub_right
    split_ifs
    · exact ih₂
    · exact Commute.zero_right A

@[simp] theorem rightWick_vacuum (w : List ι) :
    rightWick w (basisVector []) = basisVector w.reverse := by
  induction w using rightWick.induct with
  | case1 => simp [rightWick]
  | case2 i => simp [rightWick, basisVector]
  | case3 i j w ih₁ ih₂ =>
    simp only [rightWick, sub_apply, mul_apply_eq_comp, ih₁]
    by_cases h : i = j <;>
      simp only [h, ↓reduceIte, ih₂] <;>
      simp [basisVector, List.reverse_cons, h, rightSemicircular_single_append]

@[simp] theorem adjoint_rightWick_vacuum (w : List ι) :
    star (rightWick w) (basisVector []) = basisVector w := by
  induction w using rightWick.induct with
  | case1 => simp [rightWick]
  | case2 i =>
    rw [rightWick, (rightSemicircular_selfAdjoint i).star_eq]
    simp [basisVector]
  | case3 i j w ih₁ ih₂ =>
    have hc : Commute (star (rightWick (j :: w))) (semicircular i) := by
      have h := commute_rightWick (semicircular i) (semicircular_commutes_right i) (j :: w)
      have hs := congrArg star h.eq
      change _ * _ = _ * _
      simpa only [star_mul, (semicircular_selfAdjoint i).star_eq] using hs
    have hv : rightSemicircular i (basisVector ([] : List ι)) =
        semicircular i (basisVector []) := by simp [basisVector]
    rw [rightWick, star_sub (rightSemicircular i * rightWick (j :: w)) _, star_mul,
      (rightSemicircular_selfAdjoint i).star_eq,
      sub_apply, mul_apply_eq_comp]
    rw [hv, ← mul_apply_eq_comp, hc.eq, mul_apply_eq_comp, ih₁]
    by_cases h : i = j <;>
      simp only [h, ↓reduceIte, star_zero, ih₂] <;>
      simp [h, basisVector]

def algebra (ι : Type) [DecidableEq ι] : VonNeumannAlgebra (Space ι) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (Set.range (rightSemicircular (ι := ι)))
  centralizer_centralizer' := Set.centralizer_centralizer_centralizer _

 theorem mem_algebra_iff (A : Space ι →L[ℂ] Space ι) :
    A ∈ algebra ι ↔ ∀ i, Commute A (rightSemicircular i) := by
  change A ∈ StarSubalgebra.centralizer ℂ (Set.range rightSemicircular) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  simp only [Set.forall_mem_range, (rightSemicircular_selfAdjoint _).star_eq, and_self]
  exact forall_congr' fun i => eq_comm

theorem vacuum_separating (A : Space ι →L[ℂ] Space ι) (hA : A ∈ algebra ι)
    (h0 : A (basisVector []) = 0) : A = 0 := by
  have hsingle (w : List ι) : A (basisVector w) = 0 := by
    rw [← List.reverse_reverse w, ← rightWick_vacuum]
    rw [← mul_apply_eq_comp,
      (commute_rightWick A ((mem_algebra_iff A).mp hA) w.reverse).eq,
      mul_apply_eq_comp, h0, map_zero]
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change A (lp.single 2 w z) = 0
  have hz : lp.single 2 w z = z • basisVector w := by
    simp [basisVector, ← lp.single_smul]
  rw [hz, map_smul, hsingle, smul_zero]

theorem adjoint_vacuum_coefficient (A : Space ι →L[ℂ] Space ι)
    (hA : A ∈ algebra ι) (w : List ι) :
    (star A (basisVector [])) w = star ((A (basisVector [])) w.reverse) := by
  have hw : A (basisVector w) = rightWick w.reverse (A (basisVector [])) := by
    rw [← mul_apply_eq_comp,
      ← (commute_rightWick A ((mem_algebra_iff A).mp hA) w.reverse).eq,
      mul_apply_eq_comp, rightWick_vacuum, List.reverse_reverse]
  calc
    (star A (basisVector [])) w = inner ℂ (basisVector w) (star A (basisVector [])) := by
      simp [basisVector, lp.inner_single_left]
    _ = inner ℂ (A (basisVector w)) (basisVector []) :=
      ContinuousLinearMap.adjoint_inner_right A _ _
    _ = inner ℂ (rightWick w.reverse (A (basisVector []))) (basisVector []) := by rw [hw]
    _ = inner ℂ (A (basisVector [])) (star (rightWick w.reverse) (basisVector [])) :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = star ((A (basisVector [])) w.reverse) := by
      rw [adjoint_rightWick_vacuum]
      simp [basisVector, lp.inner_single_right]

 theorem vacuum_product_formula (A B : Space ι →L[ℂ] Space ι)
    (hA : A ∈ algebra ι) :
    inner ℂ (basisVector []) ((A * B) (basisVector [])) =
      ∑' w : List ι, (B (basisVector [])) w * (A (basisVector [])) w.reverse := by
  rw [mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left A,
    ← ContinuousLinearMap.star_eq_adjoint, lp.inner_eq_tsum]
  apply tsum_congr
  intro w
  rw [RCLike.inner_apply, adjoint_vacuum_coefficient A hA w]
  simp

theorem vacuum_tracial (A : Space ι →L[ℂ] Space ι) (hA : A ∈ algebra ι)
    (B : Space ι →L[ℂ] Space ι) (hB : B ∈ algebra ι) :
    inner ℂ (basisVector []) ((A * B) (basisVector [])) =
      inner ℂ (basisVector []) ((B * A) (basisVector [])) := by
  rw [vacuum_product_formula A B hA, vacuum_product_formula B A hB]
  let e : List ι ≃ List ι := ⟨List.reverse, List.reverse, List.reverse_reverse, List.reverse_reverse⟩
  calc
    (∑' w : List ι, (B (basisVector [])) w * (A (basisVector [])) w.reverse) =
        ∑' w : List ι, (B (basisVector [])) w.reverse * (A (basisVector [])) w := by
      simpa [e] using (e.tsum_eq (fun w : List ι =>
        (B (basisVector [])) w * (A (basisVector [])) w.reverse)).symm
    _ = _ := tsum_congr fun _ => mul_comm _ _

def tracialVector (ι : Type) [DecidableEq ι] : TracialVector (algebra ι) where
  vacuum := basisVector []
  norm_vacuum := by
    simp [basisVector, lp.norm_single (E := fun _ : List ι => ℂ) (p := 2)]
  tracial := vacuum_tracial
  separating := vacuum_separating

def vacuumProjection : Space ι →L[ℂ] Space ι :=
  InnerProductSpace.rankOne ℂ (basisVector []) (basisVector [])

@[simp] theorem vacuumProjection_single (w : List ι) (z : ℂ) :
    vacuumProjection (lp.single 2 w z) = if w = [] then lp.single 2 [] z else 0 := by
  by_cases h : w = []
  · subst w
    simp [vacuumProjection, basisVector, lp.inner_single_left, ← lp.single_smul]
  · simp [vacuumProjection, basisVector, lp.inner_single_left, lp.single_apply, h]

def derivativeKernel {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    Space (Fin n) →L[ℂ] Space (Fin n) :=
  ∑ r : Fin w.length, if w[r.val] = i then
    wordEval semicircular (w.take r.val) * vacuumProjection *
      wordEval semicircular (w.drop (r.val + 1)) else 0

@[simp] theorem derivativeKernel_nil {n : ℕ} (i : Fin n) :
    derivativeKernel i [] = 0 := by simp [derivativeKernel]

end Fock

namespace LabelHilbert
open scoped lp
variable {α : Type} [DecidableEq α]
abbrev Space (α : Type) := lp (fun _ : α => ℂ) 2

def basis (a : α) : Space α := lp.single 2 a 1

def coordinateIsometry (a : α) : ℂ →ₗᵢ[ℂ] Space α where
  toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : α => ℂ) 2 a
  norm_map' z := lp.norm_single (E := fun _ : α => ℂ) (p := 2) (by norm_num) a z

theorem orthogonal_coordinates (f : α → α) (hf : Function.Injective f) :
    OrthogonalFamily ℂ (fun _ : α => ℂ) (fun a => coordinateIsometry (f a)) := by
  intro a b hab x y
  change inner ℂ (lp.single (E := fun _ : α => ℂ) 2 (f a) x)
    (lp.single (E := fun _ : α => ℂ) 2 (f b) y) = 0
  rw [lp.inner_single_left, lp.single_apply_ne (E := fun _ : α => ℂ) 2 (f b) y
    (fun h => hab (hf h))]
  simp

def lift (f : α → α) (hf : Function.Injective f) : Space α →L[ℂ] Space α :=
  (orthogonal_coordinates f hf).linearIsometry.toContinuousLinearMap

@[simp] theorem lift_single (f : α → α) (hf : Function.Injective f) (a : α) (z : ℂ) :
    lift f hf (lp.single 2 a z) = lp.single 2 (f a) z :=
  (orthogonal_coordinates f hf).linearIsometry_apply_single z

@[simp] theorem lift_basis (f : α → α) (hf : Function.Injective f) (a : α) :
    lift f hf (basis a) = basis (f a) := lift_single f hf a 1

 theorem adjoint_apply (f : α → α) (hf : Function.Injective f) (x : Space α) (a : α) :
    (star (lift f hf) x) a = x (f a) := by
  have h := ContinuousLinearMap.adjoint_inner_right (lift f hf) (basis a) x
  simpa [basis, ContinuousLinearMap.star_eq_adjoint, lp.inner_single_left] using h

 theorem adjoint_single_of_inverse (f : α → α) (hf : Function.Injective f)
    (q : α → Option α) (hq : ∀ a b, q b = some a ↔ f a = b) (b : α) (z : ℂ) :
    star (lift f hf) (lp.single 2 b z) = (q b).elim 0 (fun a => lp.single 2 a z) := by
  apply lp.ext
  funext a
  rw [adjoint_apply]
  cases h : q b with
  | none =>
    have hab : f a ≠ b := fun he => by have := (hq a b).mpr he; simp [h] at this
    simp [lp.single_apply, hab]
  | some c =>
    have hfc : f c = b := (hq c b).mp h
    subst b
    change (lp.single (E := fun _ : α => ℂ) 2 (f c) z) (f a) =
      (lp.single (E := fun _ : α => ℂ) 2 c z) a
    by_cases hac : a = c
    · subst a; simp
    · rw [lp.single_apply_ne (E := fun _ : α => ℂ) 2 (f c) z (fun h => hac (hf h)),
        lp.single_apply_ne (E := fun _ : α => ℂ) 2 c z hac]

 theorem lift_mul (f g : α → α) (hf : Function.Injective f) (hg : Function.Injective g) :
    lift f hf * lift g hg = lift (f ∘ g) (hf.comp hg) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro a
  apply ContinuousLinearMap.ext
  intro z
  change lift f hf (lift g hg (lp.single 2 a z)) = _
  simp

 theorem lift_commute (f g : α → α) (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : Function.Commute f g) : Commute (lift f hf) (lift g hg) := by
  show _ * _ = _ * _
  rw [lift_mul, lift_mul]
  congr 1
  exact funext hfg

end LabelHilbert

namespace FreeTensor
variable {B N G : Type} [Group G]
abbrev Atom (B G : Type) := List B × G
abbrev Word (B N G : Type) := Atom B G × List (N × Atom B G)

def empty : Word B N G := (([], 1), [])
def push (a : Atom B G) (i : N) (w : Word B N G) : Word B N G :=
  (a, (i, w.1) :: w.2)
def append (w : Word B N G) (i : N) (a : Atom B G) : Word B N G :=
  (w.1, w.2 ++ [(i, a)])
def reverseAtom (a : Atom B G) : Atom B G := (a.1.reverse, a.2⁻¹)

@[simp] theorem reverseAtom_involutive (a : Atom B G) : reverseAtom (reverseAtom a) = a := by
  simp [reverseAtom]

def reverseAux (a : Atom B G) : List (N × Atom B G) → Word B N G
  | [] => (reverseAtom a, [])
  | (i,b) :: t => append (reverseAux b t) i (reverseAtom a)
def reverse (w : Word B N G) : Word B N G := reverseAux w.1 w.2

@[simp] theorem reverse_nil (a : Atom B G) : reverse (a, ([] : List (N × Atom B G))) =
    (reverseAtom a, []) := rfl
@[simp] theorem reverse_push (a : Atom B G) (i : N) (w : Word B N G) :
    reverse (push a i w) = append (reverse w) i (reverseAtom a) := rfl

omit [Group G] in
 theorem push_append (a b : Atom B G) (i j : N) (w : Word B N G) :
    push a i (append w j b) = append (push a i w) j b := rfl

 theorem reverse_append (w : Word B N G) (i : N) (a : Atom B G) :
    reverse (append w i a) = push (reverseAtom a) i (reverse w) := by
  rcases w with ⟨b, t⟩
  induction t generalizing b with
  | nil => rfl
  | cons c t ih =>
    rcases c with ⟨j,c⟩
    change append (reverse (append (c,t) i a)) j (reverseAtom b) = _
    rw [ih, ← push_append]
    rfl

@[simp] theorem reverse_involutive (w : Word B N G) : reverse (reverse w) = w := by
  rcases w with ⟨a,t⟩
  induction t generalizing a with
  | nil => simp
  | cons b t ih =>
    rcases b with ⟨i,b⟩
    change reverse (append (reverse (b,t)) i (reverseAtom a)) = _
    rw [reverse_append, reverseAtom_involutive, ih]
    rfl

def leftB (b : B) (w : Word B N G) : Word B N G := ((b :: w.1.1, w.1.2), w.2)
def leftN (i : N) (w : Word B N G) : Word B N G := push ([],1) i w
def leftG (g : G) (w : Word B N G) : Word B N G := ((w.1.1, g * w.1.2), w.2)
def rightB (b : B) (w : Word B N G) : Word B N G := reverse (leftB b (reverse w))
def rightN (i : N) (w : Word B N G) : Word B N G := reverse (leftN i (reverse w))
def rightG (g : G) (w : Word B N G) : Word B N G := reverse (leftG g (reverse w))

omit [Group G] in
 theorem leftB_injective (b : B) : Function.Injective (leftB (N := N) (G := G) b) := by
  rintro ⟨⟨v,g⟩,t⟩ ⟨⟨w,h⟩,s⟩ he
  simpa [leftB] using he
 theorem leftN_injective (i : N) : Function.Injective (leftN (B := B) (G := G) i) := by
  rintro ⟨a,t⟩ ⟨b,s⟩ he
  simpa [leftN, push] using he
 theorem leftG_injective (g : G) : Function.Injective (leftG (B := B) (N := N) g) := by
  rintro ⟨⟨v,h⟩,t⟩ ⟨⟨w,k⟩,s⟩ he
  simpa [leftG] using he
 theorem reverse_injective : Function.Injective (reverse (B := B) (N := N) (G := G)) :=
  Function.Involutive.injective reverse_involutive
 theorem rightB_injective (b : B) : Function.Injective (rightB (N := N) (G := G) b) :=
  reverse_injective.comp ((leftB_injective b).comp reverse_injective)
 theorem rightN_injective (i : N) : Function.Injective (rightN (B := B) (G := G) i) :=
  reverse_injective.comp ((leftN_injective i).comp reverse_injective)
 theorem rightG_injective (g : G) : Function.Injective (rightG (B := B) (N := N) g) :=
  reverse_injective.comp ((leftG_injective g).comp reverse_injective)

@[simp] theorem rightB_nil (b : B) (a : Atom B G) :
    rightB b (a, ([] : List (N × Atom B G))) = ((a.1 ++ [b],a.2),[]) := by
  simp [rightB, leftB, reverse, reverseAux, reverseAtom]
@[simp] theorem rightB_push (b : B) (a : Atom B G) (i : N) (w : Word B N G) :
    rightB b (push a i w) = push a i (rightB b w) := by
  have h (v : Word B N G) : leftB b (append v i (reverseAtom a)) =
      append (leftB b v) i (reverseAtom a) := rfl
  rw [rightB, reverse_push, h, reverse_append, reverseAtom_involutive]
  rfl
@[simp] theorem rightN_eq_append (i : N) (w : Word B N G) :
    rightN i w = append w i ([],1) := by
  rw [rightN, leftN, reverse_push, reverse_involutive]
  simp [reverseAtom]

@[simp] theorem rightG_nil (g : G) (a : Atom B G) :
    rightG g (a, ([] : List (N × Atom B G))) = ((a.1,a.2 * g⁻¹),[]) := by
  simp [rightG, leftG, reverse, reverseAux, reverseAtom]
@[simp] theorem rightG_push (g : G) (a : Atom B G) (i : N) (w : Word B N G) :
    rightG g (push a i w) = push a i (rightG g w) := by
  have h (v : Word B N G) : leftG g (append v i (reverseAtom a)) =
      append (leftG g v) i (reverseAtom a) := rfl
  rw [rightG, reverse_push, h, reverse_append, reverseAtom_involutive]
  rfl

 theorem leftB_rightB (b c : B) :
    Function.Commute (leftB (N := N) (G := G) b) (rightB c) := by
  rintro ⟨⟨v,g⟩,t⟩
  cases t with
  | nil => simp [leftB]
  | cons a t =>
    rcases a with ⟨i,a⟩
    change leftB b (rightB c (push (v,g) i (a,t))) =
      rightB c (push (b::v,g) i (a,t))
    rw [rightB_push, rightB_push]
    rfl
 theorem leftN_rightB (i : N) (b : B) :
    Function.Commute (leftN (G := G) i) (rightB b) := by
  intro w
  exact (rightB_push b ([],1) i w).symm
 theorem leftG_rightB (g : G) (b : B) :
    Function.Commute (leftG (N := N) g) (rightB b) := by
  rintro ⟨⟨v,h⟩,t⟩
  cases t with
  | nil => simp [leftG]
  | cons a t =>
    rcases a with ⟨i,a⟩
    change leftG g (rightB b (push (v,h) i (a,t))) =
      rightB b (push (v,g*h) i (a,t))
    rw [rightB_push, rightB_push]
    rfl
 theorem leftB_rightN (b : B) (i : N) :
    Function.Commute (leftB (G := G) b) (rightN i) := by
  intro w
  simp only [rightN_eq_append]
  rfl
 theorem leftN_rightN (i j : N) :
    Function.Commute (leftN (B := B) (G := G) i) (rightN j) := by
  intro w
  simp only [rightN_eq_append]
  rfl
 theorem leftG_rightN (g : G) (i : N) :
    Function.Commute (leftG (B := B) g) (rightN i) := by
  intro w
  simp only [rightN_eq_append]
  rfl
 theorem leftB_rightG (b : B) (g : G) :
    Function.Commute (leftB (N := N) b) (rightG g) := by
  rintro ⟨⟨v,h⟩,t⟩
  cases t with
  | nil => simp [leftB]
  | cons a t =>
    rcases a with ⟨i,a⟩
    change leftB b (rightG g (push (v,h) i (a,t))) =
      rightG g (push (b::v,h) i (a,t))
    rw [rightG_push, rightG_push]
    rfl
 theorem leftN_rightG (i : N) (g : G) :
    Function.Commute (leftN (B := B) i) (rightG g) := by
  intro w
  exact (rightG_push g ([],1) i w).symm
 theorem leftG_rightG (g h : G) :
    Function.Commute (leftG (B := B) (N := N) g) (rightG h) := by
  rintro ⟨⟨v,k⟩,t⟩
  cases t with
  | nil => simp [leftG, mul_assoc]
  | cons a t =>
    rcases a with ⟨i,a⟩
    change leftG g (rightG h (push (v,k) i (a,t))) =
      rightG h (push (v,g*k) i (a,t))
    rw [rightG_push, rightG_push]
    rfl

variable [DecidableEq B] [DecidableEq N] [DecidableEq G]
open scoped lp
abbrev Space (B N G : Type) := LabelHilbert.Space (Word B N G)
def basis (w : Word B N G) : Space B N G := lp.single 2 w 1

def creationB (b : B) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (leftB b) (leftB_injective b)
def creationN (i : N) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (leftN i) (leftN_injective i)
def unitaryG (g : G) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (leftG g) (leftG_injective g)
def rightCreationB (b : B) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (rightB b) (rightB_injective b)
def rightCreationN (i : N) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (rightN i) (rightN_injective i)
def rightUnitaryG (g : G) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (rightG g) (rightG_injective g)

omit [Group G] in
@[simp] theorem creationB_single (b : B) (w : Word B N G) (z : ℂ) :
    creationB b (lp.single 2 w z) = lp.single 2 (leftB b w) z :=
  LabelHilbert.lift_single _ _ _ _
@[simp] theorem creationN_single (i : N) (w : Word B N G) (z : ℂ) :
    creationN i (lp.single 2 w z) = lp.single 2 (leftN i w) z :=
  LabelHilbert.lift_single _ _ _ _
@[simp] theorem unitaryG_single (g : G) (w : Word B N G) (z : ℂ) :
    unitaryG g (lp.single 2 w z) = lp.single 2 (leftG g w) z :=
  LabelHilbert.lift_single _ _ _ _
@[simp] theorem rightCreationB_single (b : B) (w : Word B N G) (z : ℂ) :
    rightCreationB b (lp.single 2 w z) = lp.single 2 (rightB b w) z :=
  LabelHilbert.lift_single _ _ _ _
@[simp] theorem rightCreationN_single (i : N) (w : Word B N G) (z : ℂ) :
    rightCreationN i (lp.single 2 w z) = lp.single 2 (rightN i w) z :=
  LabelHilbert.lift_single _ _ _ _
@[simp] theorem rightUnitaryG_single (g : G) (w : Word B N G) (z : ℂ) :
    rightUnitaryG g (lp.single 2 w z) = lp.single 2 (rightG g w) z :=
  LabelHilbert.lift_single _ _ _ _

def removeB (b : B) (w : Word B N G) : Option (Word B N G) :=
  match w.1.1 with
  | [] => none
  | c::v => if b = c then some ((v,w.1.2),w.2) else none

def removeN (i : N) (w : Word B N G) : Option (Word B N G) :=
  if w.1 = ([],1) then match w.2 with
    | [] => none
    | (j,a)::t => if i = j then some (a,t) else none
  else none

omit [Group G] [DecidableEq N] [DecidableEq G] in
 theorem removeB_spec (b : B) (u v : Word B N G) : removeB b v = some u ↔ leftB b u = v := by
  rcases u with ⟨⟨uv,ug⟩,ut⟩
  rcases v with ⟨⟨vv,vg⟩,vt⟩
  cases vv with
  | nil => simp [removeB, leftB]
  | cons c vv =>
    by_cases h : b = c
    · subst c; simp [removeB, leftB, eq_comm]
    · simp [removeB, leftB, h]

 theorem removeN_spec (i : N) (u v : Word B N G) : removeN i v = some u ↔ leftN i u = v := by
  rcases u with ⟨ua,ut⟩
  rcases v with ⟨va,vt⟩
  by_cases h : va = ([],1)
  · subst va
    cases vt with
    | nil => simp [removeN, leftN, push]
    | cons a t =>
      rcases a with ⟨j,a⟩
      by_cases hij : i = j
      · subst j; simp [removeN, leftN, push, eq_comm]
      · simp [removeN, leftN, push, hij]
  · simp [removeN, leftN, push, h, Ne.symm h]

omit [Group G] in
 theorem annihilationB_single (b : B) (w : Word B N G) (z : ℂ) :
    star (creationB b) (lp.single 2 w z) =
      (removeB b w).elim 0 (fun a => lp.single 2 a z) :=
  LabelHilbert.adjoint_single_of_inverse _ _ _ (removeB_spec b) _ _
 theorem annihilationN_single (i : N) (w : Word B N G) (z : ℂ) :
    star (creationN i) (lp.single 2 w z) =
      (removeN i w).elim 0 (fun a => lp.single 2 a z) :=
  LabelHilbert.adjoint_single_of_inverse _ _ _ (removeN_spec i) _ _

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
 theorem right_remove_spec (f : Word B N G → Word B N G)
    (q : Word B N G → Option (Word B N G)) (hq : ∀ u v, q v = some u ↔ f u = v)
    (u v : Word B N G) :
    (q (reverse v)).map reverse = some u ↔ reverse (f (reverse u)) = v := by
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨a,ha,hu⟩
    have had : a = reverse u := by rw [← hu, reverse_involutive]
    rw [had] at ha
    rw [(hq _ _).mp ha, reverse_involutive]
  · intro h
    refine ⟨reverse u, (hq _ _).mpr ?_, reverse_involutive u⟩
    have := congrArg reverse h
    simpa using this

 theorem rightAnnihilationB_single (b : B) (w : Word B N G) (z : ℂ) :
    star (rightCreationB b) (lp.single 2 w z) =
      ((removeB b (reverse w)).map reverse).elim 0 (fun a => lp.single 2 a z) :=
  LabelHilbert.adjoint_single_of_inverse _ _ _ (right_remove_spec _ _ (removeB_spec b)) _ _
 theorem rightAnnihilationN_single (i : N) (w : Word B N G) (z : ℂ) :
    star (rightCreationN i) (lp.single 2 w z) =
      ((removeN i (reverse w)).map reverse).elim 0 (fun a => lp.single 2 a z) :=
  LabelHilbert.adjoint_single_of_inverse _ _ _ (right_remove_spec _ _ (removeN_spec i)) _ _

@[simp] theorem rightAnnihilationN_atom (i : N) (a : Atom B G) (z : ℂ) :
    star (rightCreationN i) (lp.single 2 (a,[]) z) = 0 := by
  rw [rightAnnihilationN_single]
  have hr : removeN i (reverse (a,[])) = none := by
    dsimp only [reverse_nil, removeN]
    split <;> rfl
  rw [hr]
  rfl

 theorem rightAnnihilationN_append (i j : N) (w : Word B N G) (a : Atom B G) (z : ℂ) :
    star (rightCreationN i) (lp.single 2 (append w j a) z) =
      if a = ([],1) ∧ i = j then lp.single 2 w z else 0 := by
  rw [rightAnnihilationN_single, reverse_append]
  have ha : reverseAtom a = ([],1) ↔ a = ([],1) := by
    rcases a with ⟨v,g⟩
    simp [reverseAtom]
  by_cases haa : a = ([],1)
  · subst a
    by_cases hij : i = j <;> simp [removeN, push, reverseAtom, hij]
  · simp [removeN, push, ha, haa]

@[simp] theorem rightAnnihilationB_atom_nil (b : B) (g : G) (z : ℂ) :
    star (rightCreationB (N := N) b) (lp.single 2 (([],g),[]) z) = 0 := by
  rw [rightAnnihilationB_single]
  simp [reverse_nil, reverseAtom, removeB]

 theorem rightAnnihilationB_atom_append (b c : B) (v : List B) (g : G) (z : ℂ) :
    star (rightCreationB (N := N) b) (lp.single 2 ((v ++ [c],g),[]) z) =
      if b = c then lp.single 2 ((v,g),[]) z else 0 := by
  rw [rightAnnihilationB_single]
  by_cases h : b = c <;> simp [reverse_nil, reverseAtom, removeB, h]

@[simp] theorem rightAnnihilationB_append_nil (b : B) (w : Word B N G) (i : N)
    (g : G) (z : ℂ) :
    star (rightCreationB b) (lp.single 2 (append w i ([],g)) z) = 0 := by
  rw [rightAnnihilationB_single, reverse_append]
  simp [reverseAtom, push, removeB]

 theorem rightAnnihilationB_append_append (b c : B) (w : Word B N G) (i : N)
    (v : List B) (g : G) (z : ℂ) :
    star (rightCreationB b) (lp.single 2 (append w i (v ++ [c],g)) z) =
      if b = c then lp.single 2 (append w i (v,g)) z else 0 := by
  rw [rightAnnihilationB_single, reverse_append]
  have hinv := reverse_involutive w
  simp only [reverse] at hinv
  by_cases h : b = c <;>
    simp [reverseAtom, push, removeB, h, reverse, reverseAux, append, hinv]

 theorem creationB_commutes_rightAnnihilationN (b : B) (i : N) :
    Commute (creationB (G := G) b) (star (rightCreationN i)) := by
  show _ * _ = _ * _
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change creationB b (star (rightCreationN i) (lp.single 2 w z)) =
    star (rightCreationN i) (creationB b (lp.single 2 w z))
  rcases w with ⟨a,t⟩
  induction t using List.reverseRecOn with
  | nil => simp [leftB]
  | append_singleton t c _ =>
    rcases c with ⟨j,c⟩
    change creationB b (star (rightCreationN i) (lp.single 2 (append (a,t) j c) z)) = _
    rw [rightAnnihilationN_append, creationB_single]
    change creationB b (if c = ([],1) ∧ i = j then lp.single 2 (a,t) z else 0) =
      star (rightCreationN i) (lp.single 2 (append (leftB b (a,t)) j c) z)
    rw [rightAnnihilationN_append]
    split_ifs <;> simp

 theorem creationN_commutes_rightAnnihilationB (i : N) (b : B) :
    Commute (creationN (G := G) i) (star (rightCreationB b)) := by
  show _ * _ = _ * _
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change creationN i (star (rightCreationB b) (lp.single 2 w z)) =
    star (rightCreationB b) (creationN i (lp.single 2 w z))
  rcases w with ⟨⟨av,g⟩,t⟩
  induction t using List.reverseRecOn with
  | nil =>
    induction av using List.reverseRecOn with
    | nil =>
      rw [rightAnnihilationB_atom_nil, map_zero, creationN_single]
      change 0 = star (rightCreationB b) (lp.single 2 (append empty i ([],g)) z)
      simp
    | append_singleton v c _ =>
      rw [rightAnnihilationB_atom_append, creationN_single]
      change creationN i (if b = c then lp.single 2 ((v,g),[]) z else 0) =
        star (rightCreationB b) (lp.single 2 (append empty i (v ++ [c],g)) z)
      rw [rightAnnihilationB_append_append]
      split_ifs <;> simp [leftN, push, append, empty]
  | append_singleton t c _ =>
    rcases c with ⟨j,⟨v,h⟩⟩
    rw [creationN_single]
    change creationN i (star (rightCreationB b)
      (lp.single 2 (append ((av,g),t) j (v,h)) z)) =
      star (rightCreationB b) (lp.single 2 (append (leftN i ((av,g),t)) j (v,h)) z)
    induction v using List.reverseRecOn with
    | nil => simp
    | append_singleton v c _ =>
      rw [rightAnnihilationB_append_append, rightAnnihilationB_append_append]
      split_ifs <;> simp [leftN, push, append]

end FreeTensor

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianHermite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
 def gaussianPolyIntegral (P : ℝ[X]) : ℝ := ∫ x, P.eval x ∂gaussianReal 0 1
 @[simp] theorem gaussianPolyIntegral_one : gaussianPolyIntegral 1 = 1 := by simp [gaussianPolyIntegral]
 @[simp] theorem gaussianPolyIntegral_zero : gaussianPolyIntegral 0 = 0 := by simp [gaussianPolyIntegral]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorHermite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
def productGaussian (ι : Type u2) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal Topology
namespace FiniteEntropySeparation
 variable {ι : Type u1} [Fintype ι]
 def normalKernel (s : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
    Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)-‖x‖^2/(2*s))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
def normalGradient (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) : ℝ := -x i/s*normalKernel s x
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
def smoothedDensity (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∫a,normalKernel s (x-a) ∂μ
def smoothedGradient (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) : ℝ :=
  ∫a,normalGradient s (x-a) i ∂μ
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CoordinateMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 def coordinateMask (m : Finset ι) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
    WithLp.toLp 2 (fun i => if i∈m then x i else 0)
 def coordinateMaskLinear (m : Finset ι) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun := coordinateMask m
  map_add' x y := by ext i; simp only [coordinateMask,PiLp.toLp_apply,PiLp.add_apply]; split_ifs <;> simp
  map_smul' r x := by ext i; simp only [coordinateMask,PiLp.toLp_apply,PiLp.smul_apply,smul_eq_mul,RingHom.id_apply]; split_ifs <;> simp
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 theorem hermitianMatrix_add {n d : ℕ} (a b : MatrixCoordinates n d) (i : Fin n) :
    hermitianMatrix (a+b) i = hermitianMatrix a i + hermitianMatrix b i := by
  ext j k
  simp only [hermitianMatrix, PiLp.add_apply, Matrix.add_apply]
  split_ifs <;> push_cast <;> ring
 theorem hermitianMatrix_smul {n d : ℕ} (r : ℝ) (a : MatrixCoordinates n d) (i : Fin n) :
    hermitianMatrix (r • a) i = r • hermitianMatrix a i := by
  ext j k
  simp only [hermitianMatrix, PiLp.smul_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  split_ifs <;> push_cast <;> ring
 def hermitianChart (n d : ℕ) : MatrixCoordinates n d →ₗ[ℝ] (Fin n → Matrix (Fin d) (Fin d) ℂ) where
  toFun := hermitianMatrix
  map_add' a b := funext (hermitianMatrix_add a b)
  map_smul' r a := funext (hermitianMatrix_smul r a)
 theorem hermitianMatrix_isHermitian {n d : ℕ} (a : MatrixCoordinates n d) (i : Fin n) :
    (hermitianMatrix a i).IsHermitian := by
  ext j k
  simp only [Matrix.conjTranspose_apply, hermitianMatrix]
  by_cases h : j=k
  · subst k; simp
  · have h' : k ≠ j := Ne.symm h
    rcases lt_or_gt_of_ne h with hjk | hkj
    · simp [h,h',hjk,not_lt_of_gt hjk, Complex.conj_ofReal, sub_eq_add_neg]
    · simp [h,h',hkj,not_lt_of_gt hkj, Complex.conj_ofReal, sub_eq_add_neg]
 theorem hermitianMatrix_normSq {n d : ℕ} (a : MatrixCoordinates n d) (i : Fin n) (j k : Fin d) :
    Complex.normSq (hermitianMatrix a i j k) = (a (i,j,k)^2 + a (i,k,j)^2)/2 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold hermitianMatrix
  split_ifs with h hlt
  · subst k; simp [Complex.normSq_ofReal]; ring
  · rw [Complex.normSq_div, Complex.normSq_ofReal, hs]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  · rw [Complex.normSq_div, Complex.normSq_ofReal, hs]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
 theorem hermitianMatrix_frobenius {n d : ℕ} (a : MatrixCoordinates n d) (i : Fin n) :
    (∑ j, ∑ k, Complex.normSq (hermitianMatrix a i j k)) = ∑ j, ∑ k, a (i,j,k)^2 := by
  simp_rw [hermitianMatrix_normSq, add_div]
  simp_rw [sum_add_distrib]
  have he : (∑ j : Fin d, ∑ k : Fin d, a (i,k,j)^2 / 2) = ∑ j : Fin d, ∑ k : Fin d, a (i,j,k)^2 / 2 := sum_comm
  rw [he]
  simp_rw [← sum_div]
  ring
 theorem hermitianChart_normSq {n d : ℕ} (a : MatrixCoordinates n d) :
    (∑ i, ∑ j, ∑ k, Complex.normSq (hermitianMatrix a i j k)) = ‖a‖^2 := by
  simp_rw [hermitianMatrix_frobenius]
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 def hermitianBasis {d : ℕ} (j k : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  if j=k then Matrix.single j j 1 else if j<k then
    ((Real.sqrt 2 : ℂ)⁻¹) • (Matrix.single j k 1 + Matrix.single k j 1)
  else (Complex.I * (Real.sqrt 2 : ℂ)⁻¹) • (Matrix.single k j 1 - Matrix.single j k 1)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 def coordinateDerivative (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  deriv (fun t => f (Function.update x i t)) (x i)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.PolynomialFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 def IsRealPolynomial (f : (ι → ℝ) → ℝ) : Prop := ∃ P : MvPolynomial ι ℝ, f = fun x => MvPolynomial.eval x P
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.ComplexPolynomialFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 def IsComplexPolynomial (f : (ι → ℝ) → ℂ) : Prop :=
  IsRealPolynomial (fun x => (f x).re) ∧ IsRealPolynomial (fun x => (f x).im)
 def complexCoordinateDerivative (f : (ι → ℝ) → ℂ) (i : ι) (x : ι → ℝ) : ℂ :=
  deriv (fun t => f (Function.update x i t)) (x i)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
 abbrev MatrixIndex (n d : ℕ) := Fin n × Fin d × Fin d
 def coordinateMatrix {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  hermitianMatrix (WithLp.toLp 2 x) i
 variable {ι : Type u1} {κ : Type u2} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
 def IsMatrixPolynomial (A : (ι → ℝ) → Matrix d d ℂ) : Prop := ∀ j k, IsComplexPolynomial (fun x => A x j k)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixWordDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 variable {α : Type u1} {d : ℕ}
 def matrixWord (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) : Matrix (Fin d) (Fin d) ℂ := (w.map A).prod
 @[simp] theorem matrixWord_nil (A : α → Matrix (Fin d) (Fin d) ℂ) : matrixWord A [] = 1 := rfl
 @[simp] theorem matrixWord_cons (A : α → Matrix (Fin d) (Fin d) ℂ) (a : α) (w : List α) : matrixWord A (a::w) = A a*matrixWord A w := rfl
 def cyclicMatrixWord (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) (r : Fin w.length) : Matrix (Fin d) (Fin d) ℂ :=
   matrixWord A (w.drop (r.val+1))*matrixWord A (w.take r.val)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev WordPolynomial (n : ℕ) := List (Fin n) →₀ ℂ

def polynomialVector {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) : WordPolynomial n →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ (fun w => wordEval X w τ.vacuum)

def polynomialDerivative {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (i : Fin n) : WordPolynomial n →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (derivativeMoment τ X i)

def fisherTest {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (i : Fin n) (p : WordPolynomial n) : ℝ :=
  2 * (polynomialDerivative τ X i p).re - ‖polynomialVector τ X p‖ ^ 2

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TracialRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
theorem commute_add_star_of_boundary {A : Type u1} [Ring A] [StarRing A]
    (l r q : A) (hlr : Commute l r)
    (hrl : star r * l = l * star r + q) (hq : star q = q) :
    Commute (l + star l) (r + star r) := by
  have hls : star l * r = r * star l + q := by
    simpa only [star_mul, star_add, star_star, hq] using congrArg star hrl
  have hss : star l * star r = star r * star l := hlr.star_star.eq
  show _ * _ = _ * _
  simp only [add_mul, mul_add]
  rw [hlr.eq, hls, hss, hrl]
  abel

namespace LabelHilbert
variable {α : Type} [DecidableEq α]

theorem lift_inverse (f g : α → α) (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : Function.LeftInverse g f) (hgf : Function.RightInverse g f) :
    star (lift f hf) = lift g hg := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro a
  apply ContinuousLinearMap.ext
  intro z
  change star (lift f hf) (lp.single 2 a z) = lift g hg (lp.single 2 a z)
  rw [adjoint_single_of_inverse f hf (fun b => some (g b)), lift_single]
  · rfl
  · intro a b
    simp only [Option.some.injEq]
    constructor
    · intro h
      rw [← h, hgf b]
    · intro h
      rw [← h, hfg a]

def keepLinear (P : α → Prop) [DecidablePred P] : Space α →ₗ[ℂ] Space α where
  toFun x := ⟨fun a => if P a then x a else 0, (lp.memℓp x).mono' (by
    intro a
    split_ifs <;> simp)⟩
  map_add' x y := by
    apply lp.ext
    funext a
    change (if P a then x a + y a else 0) =
      (if P a then x a else 0) + (if P a then y a else 0)
    by_cases h : P a <;> simp [h]
  map_smul' c x := by
    apply lp.ext
    funext a
    by_cases h : P a <;> simp [h]

def keep (P : α → Prop) [DecidablePred P] : Space α →L[ℂ] Space α :=
  (keepLinear P).mkContinuous 1 (by
    intro x
    simp only [one_mul]
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro a
    change ‖if P a then x a else 0‖ ≤ ‖x a‖
    split_ifs <;> simp)

omit [DecidableEq α] in
@[simp] theorem keep_apply (P : α → Prop) [DecidablePred P] (x : Space α) (a : α) :
    keep P x a = if P a then x a else 0 := rfl

 theorem keep_single (P : α → Prop) [DecidablePred P] (a : α) (z : ℂ) :
    keep P (lp.single 2 a z) = if P a then lp.single 2 a z else 0 := by
  apply lp.ext
  funext b
  by_cases h : b = a
  · subst b; split_ifs <;> simp_all
  · by_cases ha : P a <;> by_cases hb : P b <;>
      simp [ha, hb, lp.single_apply, h]

@[simp] theorem star_keep (P : α → Prop) [DecidablePred P] : star (keep P) = keep P := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext a
  have h := ContinuousLinearMap.adjoint_inner_right (keep P) (basis a) x
  change inner ℂ (basis a) (star (keep P) x) = inner ℂ (keep P (basis a)) x at h
  rw [basis, keep_single] at h
  by_cases ha : P a <;> simpa [ha, lp.inner_single_left] using h

end LabelHilbert
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
@[simp] theorem leftG_one (w : Word B N G) : leftG 1 w = w := by
  rcases w with ⟨⟨v,g⟩,t⟩
  simp [leftG]

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
@[simp] theorem leftG_mul (g h : G) (w : Word B N G) :
    leftG (g*h) w = leftG g (leftG h w) := by
  simp [leftG, mul_assoc]

@[simp] theorem unitaryG_one : unitaryG (B := B) (N := N) (1 : G) = 1 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro a
  apply ContinuousLinearMap.ext
  intro z
  change unitaryG 1 (lp.single 2 a z) = lp.single 2 a z
  rw [unitaryG_single, leftG_one]

@[simp] theorem unitaryG_mul (g h : G) :
    unitaryG (B := B) (N := N) (g*h) = unitaryG g * unitaryG h := by
  unfold unitaryG
  rw [LabelHilbert.lift_mul]
  congr 1
  exact funext (leftG_mul g h)

@[simp] theorem star_unitaryG (g : G) :
    star (unitaryG (B := B) (N := N) g) = unitaryG g⁻¹ := by
  apply LabelHilbert.lift_inverse
  · intro w; rw [← leftG_mul]; simp
  · intro w; rw [← leftG_mul]; simp

@[simp] theorem star_rightUnitaryG (g : G) :
    star (rightUnitaryG (B := B) (N := N) g) = rightUnitaryG g⁻¹ := by
  apply LabelHilbert.lift_inverse
  · intro w; simp [rightG, ← leftG_mul]
  · intro w; simp [rightG, ← leftG_mul]

 theorem unitaryG_commutes_rightCreationB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (rightCreationB b) :=
  LabelHilbert.lift_commute _ _ _ _ (leftG_rightB g b)

 theorem unitaryG_commutes_rightCreationN (g : G) (i : N) :
    Commute (unitaryG (B := B) g) (rightCreationN i) :=
  LabelHilbert.lift_commute _ _ _ _ (leftG_rightN g i)

 theorem creationB_commutes_rightUnitaryG (b : B) (g : G) :
    Commute (creationB (N := N) b) (rightUnitaryG g) :=
  LabelHilbert.lift_commute _ _ _ _ (leftB_rightG b g)

 theorem creationN_commutes_rightUnitaryG (i : N) (g : G) :
    Commute (creationN (B := B) i) (rightUnitaryG g) :=
  LabelHilbert.lift_commute _ _ _ _ (leftN_rightG i g)

 theorem unitaryG_commutes_rightUnitaryG (g h : G) :
    Commute (unitaryG (B := B) (N := N) g) (rightUnitaryG h) :=
  LabelHilbert.lift_commute _ _ _ _ (leftG_rightG g h)

 theorem unitaryG_commutes_rightAnnihilationB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (star (rightCreationB b)) := by
  have h := (unitaryG_commutes_rightCreationB (N := N) g⁻¹ b).star_star
  simpa using h

 theorem unitaryG_commutes_rightAnnihilationN (g : G) (i : N) :
    Commute (unitaryG (B := B) g) (star (rightCreationN i)) := by
  have h := (unitaryG_commutes_rightCreationN (B := B) g⁻¹ i).star_star
  simpa using h

 theorem annihilationB_commutes_rightUnitaryG (b : B) (g : G) :
    Commute (star (creationB (N := N) b)) (rightUnitaryG g) := by
  have h := (creationB_commutes_rightUnitaryG (N := N) b g⁻¹).star_star
  simpa using h

 theorem annihilationN_commutes_rightUnitaryG (i : N) (g : G) :
    Commute (star (creationN (B := B) i)) (rightUnitaryG g) := by
  have h := (creationN_commutes_rightUnitaryG (B := B) i g⁻¹).star_star
  simpa using h

def signalBoundary : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.keep (fun w : Word B N G => w.1.1 = [] ∧ w.2 = [])

def vacuumBoundary : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.keep (fun w : Word B N G => w = empty)

omit [Group G] in
@[simp] theorem signalBoundary_single (w : Word B N G) (z : ℂ) :
    signalBoundary (lp.single 2 w z) =
      if w.1.1 = [] ∧ w.2 = [] then lp.single 2 w z else 0 :=
  LabelHilbert.keep_single _ _ _

@[simp] theorem vacuumBoundary_single (w : Word B N G) (z : ℂ) :
    vacuumBoundary (lp.single 2 w z) = if w = empty then lp.single 2 w z else 0 :=
  LabelHilbert.keep_single _ _ _

 theorem rightAnnihilationN_creationN (i j : N) :
    star (rightCreationN (B := B) (G := G) i) * creationN j =
      creationN j * star (rightCreationN i) + if i = j then vacuumBoundary else 0 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (rightCreationN i) (creationN j (lp.single 2 w z)) =
    creationN j (star (rightCreationN i) (lp.single 2 w z)) +
      (if i = j then vacuumBoundary else 0) (lp.single 2 w z)
  rcases w with ⟨a,t⟩
  induction t using List.reverseRecOn with
  | nil =>
    rw [rightAnnihilationN_atom, map_zero, zero_add, creationN_single]
    change star (rightCreationN i) (lp.single 2 (append empty j a) z) = _
    rw [rightAnnihilationN_append]
    by_cases ha : a = ([],1) <;> by_cases hij : i = j <;>
      simp [ha, hij, empty]
  | append_singleton t c _ =>
    rcases c with ⟨k,c⟩
    rw [creationN_single]
    change star (rightCreationN i) (lp.single 2 (append (leftN j (a,t)) k c) z) =
      creationN j (star (rightCreationN i) (lp.single 2 (append (a,t) k c) z)) + _
    rw [rightAnnihilationN_append, rightAnnihilationN_append]
    by_cases hij : i = j <;> simp only [hij, ↓reduceIte, zero_apply]
    all_goals simp only [vacuumBoundary_single, empty, Prod.mk.injEq,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, ↓reduceIte, add_zero]
    all_goals split_ifs <;> simp

 theorem rightAnnihilationB_creationB_atom (b c : B) (v : List B) (g : G) (z : ℂ) :
    star (rightCreationB (N := N) b) (creationB c (lp.single 2 ((v,g),[]) z)) =
      creationB c (star (rightCreationB b) (lp.single 2 ((v,g),[]) z)) +
        (if b = c then signalBoundary else 0) (lp.single 2 ((v,g),[]) z) := by
  induction v using List.reverseRecOn with
  | nil =>
    rw [rightAnnihilationB_atom_nil, map_zero, zero_add, creationB_single]
    simp only [leftB]
    rw [show [c] = [] ++ [c] from rfl, rightAnnihilationB_atom_append]
    by_cases h : b = c <;> simp only [h, ↓reduceIte, signalBoundary_single,
      and_self, zero_apply]
  | append_singleton v a _ =>
    rw [rightAnnihilationB_atom_append, creationB_single]
    simp only [leftB] at *
    rw [show c :: (v ++ [a]) = (c :: v) ++ [a] from rfl, rightAnnihilationB_atom_append]
    by_cases hc : b = c <;> simp only [hc, ↓reduceIte, signalBoundary_single,
      List.append_eq_nil_iff, List.cons_ne_nil, and_false, false_and,
      zero_apply, add_zero]
    all_goals split_ifs <;> simp [leftB]

 theorem rightAnnihilationB_creationB_append (b c : B) (w : Word B N G) (i : N)
    (a : Atom B G) (z : ℂ) :
    star (rightCreationB b) (creationB c (lp.single 2 (append w i a) z)) =
      creationB c (star (rightCreationB b) (lp.single 2 (append w i a) z)) := by
  rcases a with ⟨v,g⟩
  rw [creationB_single]
  change star (rightCreationB b) (lp.single 2 (append (leftB c w) i (v,g)) z) = _
  induction v using List.reverseRecOn with
  | nil => rw [rightAnnihilationB_append_nil, rightAnnihilationB_append_nil, map_zero]
  | append_singleton v a _ =>
    rw [rightAnnihilationB_append_append, rightAnnihilationB_append_append]
    by_cases h : b = a <;> simp only [h, ↓reduceIte, map_zero, creationB_single]
    rfl

 theorem rightAnnihilationB_creationB (b c : B) :
    star (rightCreationB (N := N) (G := G) b) * creationB c =
      creationB c * star (rightCreationB b) + if b = c then signalBoundary else 0 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (rightCreationB b) (creationB c (lp.single 2 w z)) =
    creationB c (star (rightCreationB b) (lp.single 2 w z)) +
      (if b = c then signalBoundary else 0) (lp.single 2 w z)
  rcases w with ⟨⟨v,g⟩,t⟩
  induction t using List.reverseRecOn with
  | nil => exact rightAnnihilationB_creationB_atom b c v g z
  | append_singleton t d _ =>
    rcases d with ⟨k,a⟩
    change star (rightCreationB b) (creationB c (lp.single 2 (append ((v,g),t) k a) z)) = _
    rw [rightAnnihilationB_creationB_append]
    by_cases h : b = c <;> simp [h, append]

def semicircularB (b : B) : Space B N G →L[ℂ] Space B N G := creationB b + star (creationB b)
def semicircularN (i : N) : Space B N G →L[ℂ] Space B N G := creationN i + star (creationN i)
def rightSemicircularB (b : B) : Space B N G →L[ℂ] Space B N G :=
  rightCreationB b + star (rightCreationB b)
def rightSemicircularN (i : N) : Space B N G →L[ℂ] Space B N G :=
  rightCreationN i + star (rightCreationN i)

omit [Group G] in
@[simp] theorem star_semicircularB (b : B) :
    star (semicircularB (N := N) (G := G) b) = semicircularB b := by
  exact IsSelfAdjoint.add_star_self (creationB b)
@[simp] theorem star_semicircularN (i : N) :
    star (semicircularN (B := B) (G := G) i) = semicircularN i := by
  exact IsSelfAdjoint.add_star_self (creationN i)
@[simp] theorem star_rightSemicircularB (b : B) :
    star (rightSemicircularB (N := N) (G := G) b) = rightSemicircularB b := by
  exact IsSelfAdjoint.add_star_self (rightCreationB b)
@[simp] theorem star_rightSemicircularN (i : N) :
    star (rightSemicircularN (B := B) (G := G) i) = rightSemicircularN i := by
  exact IsSelfAdjoint.add_star_self (rightCreationN i)

 theorem semicircularB_commutes_rightB (b c : B) :
    Commute (semicircularB (N := N) (G := G) b) (rightSemicircularB c) := by
  apply commute_add_star_of_boundary _ _ _
    (LabelHilbert.lift_commute _ _ _ _ (leftB_rightB b c))
    (rightAnnihilationB_creationB c b)
  split_ifs <;> simp [signalBoundary]

 theorem semicircularN_commutes_rightN (i j : N) :
    Commute (semicircularN (B := B) (G := G) i) (rightSemicircularN j) := by
  apply commute_add_star_of_boundary _ _ _
    (LabelHilbert.lift_commute _ _ _ _ (leftN_rightN i j))
    (rightAnnihilationN_creationN j i)
  split_ifs <;> simp [vacuumBoundary]

 theorem semicircularB_commutes_rightN (b : B) (i : N) :
    Commute (semicircularB (G := G) b) (rightSemicircularN i) := by
  have h : Commute (creationB (G := G) b) (rightCreationN i) :=
    LabelHilbert.lift_commute _ _ _ _ (leftB_rightN b i)
  have hs := creationB_commutes_rightAnnihilationN (G := G) b i
  have hsl : Commute (star (creationB (G := G) b)) (rightCreationN i) := by
    simpa using hs.star_star
  exact (h.add_right hs).add_left (hsl.add_right h.star_star)

 theorem semicircularN_commutes_rightB (i : N) (b : B) :
    Commute (semicircularN (G := G) i) (rightSemicircularB b) := by
  have h : Commute (creationN (G := G) i) (rightCreationB b) :=
    LabelHilbert.lift_commute _ _ _ _ (leftN_rightB i b)
  have hs := creationN_commutes_rightAnnihilationB (G := G) i b
  have hsl : Commute (star (creationN (G := G) i)) (rightCreationB b) := by
    simpa using hs.star_star
  exact (h.add_right hs).add_left (hsl.add_right h.star_star)

 theorem semicircularB_commutes_rightG (b : B) (g : G) :
    Commute (semicircularB (N := N) b) (rightUnitaryG g) :=
  (creationB_commutes_rightUnitaryG b g).add_left (annihilationB_commutes_rightUnitaryG b g)

 theorem semicircularN_commutes_rightG (i : N) (g : G) :
    Commute (semicircularN (B := B) i) (rightUnitaryG g) :=
  (creationN_commutes_rightUnitaryG i g).add_left (annihilationN_commutes_rightUnitaryG i g)

 theorem unitaryG_commutes_rightB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (rightSemicircularB b) :=
  (unitaryG_commutes_rightCreationB g b).add_right (unitaryG_commutes_rightAnnihilationB g b)

 theorem unitaryG_commutes_rightN (g : G) (i : N) :
    Commute (unitaryG (B := B) g) (rightSemicircularN i) :=
  (unitaryG_commutes_rightCreationN g i).add_right (unitaryG_commutes_rightAnnihilationN g i)

abbrev Generator (B N G : Type) := B ⊕ N ⊕ G

def leftGenerator : Generator B N G → Space B N G →L[ℂ] Space B N G
  | .inl b => semicircularB b
  | .inr (.inl i) => semicircularN i
  | .inr (.inr g) => unitaryG g

def rightGenerator : Generator B N G → Space B N G →L[ℂ] Space B N G
  | .inl b => rightSemicircularB b
  | .inr (.inl i) => rightSemicircularN i
  | .inr (.inr g) => rightUnitaryG g

def inverseGenerator : Generator B N G → Generator B N G
  | .inl b => .inl b
  | .inr (.inl i) => .inr (.inl i)
  | .inr (.inr g) => .inr (.inr g⁻¹)

@[simp] theorem star_leftGenerator (k : Generator B N G) :
    star (leftGenerator k) = leftGenerator (inverseGenerator k) := by
  rcases k with b | (i | g) <;> simp [leftGenerator, inverseGenerator]

@[simp] theorem star_rightGenerator (k : Generator B N G) :
    star (rightGenerator k) = rightGenerator (inverseGenerator k) := by
  rcases k with b | (i | g) <;> simp [rightGenerator, inverseGenerator]

 theorem generators_commute (j k : Generator B N G) :
    Commute (leftGenerator j) (rightGenerator k) := by
  rcases j with b | (i | g) <;> rcases k with c | (j | h)
  · exact semicircularB_commutes_rightB b c
  · exact semicircularB_commutes_rightN b j
  · exact semicircularB_commutes_rightG b h
  · exact semicircularN_commutes_rightB i c
  · exact semicircularN_commutes_rightN i j
  · exact semicircularN_commutes_rightG i h
  · exact unitaryG_commutes_rightB g c
  · exact unitaryG_commutes_rightN g j
  · exact unitaryG_commutes_rightUnitaryG g h

def algebra (B N G : Type) [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] :
    VonNeumannAlgebra (Space B N G) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (Set.range rightGenerator)
  centralizer_centralizer' := Set.centralizer_centralizer_centralizer _

 theorem mem_algebra_iff (A : Space B N G →L[ℂ] Space B N G) :
    A ∈ algebra B N G ↔ ∀ k : Generator B N G, Commute A (rightGenerator k) := by
  change A ∈ StarSubalgebra.centralizer ℂ (Set.range rightGenerator) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h k
    exact (h _ ⟨k,rfl⟩).1.symm
  · rintro h _ ⟨k,rfl⟩
    exact ⟨(h k).eq.symm, by rw [star_rightGenerator]; exact (h _).eq.symm⟩

def rightWick : Word B N G → Space B N G →L[ℂ] Space B N G
  | (([],g),[]) => rightUnitaryG g
  | (([b],g),t) => rightSemicircularB b * rightWick (([],g),t)
  | ((b::c::v,g),t) => rightSemicircularB b * rightWick ((c::v,g),t) -
      if b = c then rightWick ((v,g),t) else 0
  | (([],g),[(i,a)]) => rightUnitaryG g * (rightSemicircularN i * rightWick (a,[]))
  | (([],g),(i,a)::(j,d)::t) => rightUnitaryG g *
      (rightSemicircularN i * rightWick (a,(j,d)::t) -
        if a = ([],1) ∧ i = j then rightWick (d,t) else 0)
termination_by w => (w.2.length, w.1.1.length)

 theorem commute_rightWick (A : Space B N G →L[ℂ] Space B N G)
    (hA : ∀ k : Generator B N G, Commute A (rightGenerator k)) (w : Word B N G) :
    Commute A (rightWick w) := by
  induction w using rightWick.induct with
  | case1 g =>
    rw [rightWick]
    exact hA (.inr (.inr g))
  | case2 b g t ih =>
    rw [rightWick]
    exact (hA (.inl b)).mul_right ih
  | case3 b c v g t ih₁ ih₂ =>
    rw [rightWick]
    apply ((hA (.inl b)).mul_right ih₁).sub_right
    split_ifs
    · exact ih₂
    · exact Commute.zero_right A
  | case4 g i a ih =>
    rw [rightWick]
    exact (hA (.inr (.inr g))).mul_right ((hA (.inr (.inl i))).mul_right ih)
  | case5 g i a j d t ih₁ ih₂ =>
    rw [rightWick]
    apply (hA (.inr (.inr g))).mul_right
    apply ((hA (.inr (.inl i))).mul_right ih₁).sub_right
    split_ifs
    · exact ih₂
    · exact Commute.zero_right A

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
@[simp] theorem reverse_empty : reverse (B := B) (N := N) (G := G) empty = empty := by
  simp [empty, reverseAtom]

@[simp] theorem rightUnitaryG_basis_reverse (g : G) (w : Word B N G) :
    rightUnitaryG g (basis (reverse w)) = basis (reverse (leftG g w)) := by
  simp [basis, rightG]

 theorem rightSemicircularB_basis_reverse (b : B) (w : Word B N G) :
    rightSemicircularB b (basis (reverse w)) = basis (reverse (leftB b w)) +
      (removeB b w).elim 0 (fun a => basis (reverse a)) := by
  rw [rightSemicircularB, add_apply, basis, rightCreationB_single, rightAnnihilationB_single,
    reverse_involutive]
  simp only [rightB, reverse_involutive]
  cases removeB b w <;> rfl

 theorem rightSemicircularN_basis_reverse (i : N) (w : Word B N G) :
    rightSemicircularN i (basis (reverse w)) = basis (reverse (leftN i w)) +
      (removeN i w).elim 0 (fun a => basis (reverse a)) := by
  rw [rightSemicircularN, add_apply, basis, rightCreationN_single, rightAnnihilationN_single,
    reverse_involutive]
  simp only [rightN, reverse_involutive]
  cases removeN i w <;> rfl

@[simp] theorem rightWick_vacuum (w : Word B N G) :
    rightWick w (basis empty) = basis (reverse w) := by
  induction w using rightWick.induct with
  | case1 g => simp [rightWick, basis, empty, reverseAtom]
  | case2 b g t ih =>
    rw [rightWick, mul_apply_eq_comp, ih, rightSemicircularB_basis_reverse]
    simp [removeB, leftB]
  | case3 b c v g t ih₁ ih₂ =>
    rw [rightWick, sub_apply, mul_apply_eq_comp, ih₁, rightSemicircularB_basis_reverse]
    by_cases h : b = c <;> simp [h, removeB, leftB, ih₂]
  | case4 g i a ih =>
    rw [rightWick, mul_apply_eq_comp, mul_apply_eq_comp, ih,
      rightSemicircularN_basis_reverse]
    have h : removeN i (a, ([] : List (N × Atom B G))) = none := by
      simp only [removeN]; split <;> rfl
    simp [h, leftN, push, leftG]
  | case5 g i a j d t ih₁ ih₂ =>
    rw [rightWick, mul_apply_eq_comp, sub_apply, mul_apply_eq_comp, ih₁,
      rightSemicircularN_basis_reverse]
    by_cases ha : a = ([],1) <;> by_cases hij : i = j <;>
      simp [ha, hij, ih₂, removeN, leftN, push, leftG]

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
@[simp] theorem inverseGenerator_involutive (k : Generator B N G) :
    inverseGenerator (inverseGenerator k) = k := by
  rcases k with b | (i | g) <;> simp [inverseGenerator]

omit [Group G] in
 theorem semicircularB_basis (b : B) (w : Word B N G) :
    semicircularB b (basis w) = basis (leftB b w) + (removeB b w).elim 0 basis := by
  simp only [semicircularB, add_apply, basis, creationB_single, annihilationB_single]
  rfl

 theorem semicircularN_basis (i : N) (w : Word B N G) :
    semicircularN i (basis w) = basis (leftN i w) + (removeN i w).elim 0 basis := by
  simp only [semicircularN, add_apply, basis, creationN_single, annihilationN_single]
  rfl

@[simp] theorem unitaryG_basis (g : G) (w : Word B N G) :
    unitaryG g (basis w) = basis (leftG g w) := by simp [basis]

@[simp] theorem adjoint_rightGenerator_vacuum (k : Generator B N G) :
    star (rightGenerator k) (basis empty) = leftGenerator k (basis empty) := by
  rcases k with b | (i | g)
  · simp only [rightGenerator, leftGenerator, star_rightSemicircularB]
    simp [rightSemicircularB, semicircularB, basis, empty,
      annihilationB_single, removeB, leftB]
  · simp only [rightGenerator, leftGenerator, star_rightSemicircularN]
    simp [rightSemicircularN, semicircularN, basis, empty,
      annihilationN_single, removeN, leftN, append, push]
  · simp [rightGenerator, leftGenerator, basis, empty, leftG]

 theorem adjoint_right_mul_vacuum (A : Space B N G →L[ℂ] Space B N G)
    (h : ∀ j : Generator B N G, Commute (leftGenerator j) A) (k : Generator B N G) :
    star (rightGenerator k * A) (basis empty) = leftGenerator k (star A (basis empty)) := by
  have hc : Commute (leftGenerator k) (star A) := by
    simpa only [star_leftGenerator, inverseGenerator_involutive] using (h (inverseGenerator k)).star_star
  rw [star_mul, mul_apply_eq_comp, adjoint_rightGenerator_vacuum,
    ← mul_apply_eq_comp, hc.eq.symm, mul_apply_eq_comp]

 theorem adjoint_rightB_mul_vacuum (A : Space B N G →L[ℂ] Space B N G)
    (h : ∀ j : Generator B N G, Commute (leftGenerator j) A) (b : B) :
    star (rightSemicircularB (N := N) (G := G) b * A) (basis empty) = semicircularB b (star A (basis empty)) :=
  adjoint_right_mul_vacuum A h (.inl b)

 theorem adjoint_rightN_mul_vacuum (A : Space B N G →L[ℂ] Space B N G)
    (h : ∀ j : Generator B N G, Commute (leftGenerator j) A) (i : N) :
    star (rightSemicircularN (B := B) (G := G) i * A) (basis empty) = semicircularN i (star A (basis empty)) :=
  adjoint_right_mul_vacuum A h (.inr (.inl i))

 theorem adjoint_rightG_mul_vacuum (A : Space B N G →L[ℂ] Space B N G)
    (h : ∀ j : Generator B N G, Commute (leftGenerator j) A) (g : G) :
    star (rightUnitaryG (B := B) (N := N) g * A) (basis empty) = unitaryG g (star A (basis empty)) :=
  adjoint_right_mul_vacuum A h (.inr (.inr g))

 theorem rightWick_commutesLeft (w : Word B N G) (k : Generator B N G) :
    Commute (leftGenerator k) (rightWick w) :=
  commute_rightWick _ (generators_commute k) w

@[simp] theorem adjoint_rightWick_vacuum (w : Word B N G) :
    star (rightWick w) (basis empty) = basis w := by
  induction w using rightWick.induct with
  | case1 g => simp [rightWick, basis, empty]
  | case2 b g t ih =>
    rw [rightWick, adjoint_rightB_mul_vacuum (B := B) (N := N) (G := G) _ (rightWick_commutesLeft _) b, ih]
    simp [semicircularB_basis, removeB, leftB]
  | case3 b c v g t ih₁ ih₂ =>
    rw [rightWick, star_sub (R := Space B N G →L[ℂ] Space B N G) _ _, sub_apply,
      adjoint_rightB_mul_vacuum (B := B) (N := N) (G := G) _ (rightWick_commutesLeft _) b, ih₁]
    by_cases h : b = c <;> simp [h, ih₂, semicircularB_basis, removeB, leftB]
  | case4 g i a ih =>
    have hc (k : Generator B N G) : Commute (leftGenerator k)
        (rightSemicircularN i * rightWick (a, ([] : List (N × Atom B G)))) :=
      (generators_commute k (.inr (.inl i))).mul_right (rightWick_commutesLeft _ k)
    rw [rightWick, adjoint_rightG_mul_vacuum (B := B) (N := N) (G := G) _ hc g,
      adjoint_rightN_mul_vacuum (B := B) (N := N) (G := G) _ (rightWick_commutesLeft _) i, ih]
    have hn : removeN i (a, ([] : List (N × Atom B G))) = none := by
      simp only [removeN]; split <;> rfl
    simp [semicircularN_basis, hn, leftN, push, leftG]
  | case5 g i a j d t ih₁ ih₂ =>
    have hc (k : Generator B N G) : Commute (leftGenerator k)
        (rightSemicircularN i * rightWick (a,(j,d)::t) -
          if a = ([],1) ∧ i = j then rightWick (d,t) else 0) := by
      apply ((generators_commute k (.inr (.inl i))).mul_right (rightWick_commutesLeft _ k)).sub_right
      split_ifs
      · exact rightWick_commutesLeft _ k
      · exact Commute.zero_right _
    rw [rightWick, adjoint_rightG_mul_vacuum (B := B) (N := N) (G := G) _ hc g,
      star_sub (R := Space B N G →L[ℂ] Space B N G) _ _, sub_apply,
      adjoint_rightN_mul_vacuum (B := B) (N := N) (G := G) _ (rightWick_commutesLeft _) i, ih₁]
    by_cases ha : a = ([],1) <;> by_cases hij : i = j <;>
      simp [ha, hij, ih₂, semicircularN_basis, removeN, leftN, push, leftG]

theorem vacuum_separating (A : Space B N G →L[ℂ] Space B N G) (hA : A ∈ algebra B N G)
    (h0 : A (basis empty) = 0) : A = 0 := by
  have hsingle (w : Word B N G) : A (basis w) = 0 := by
    rw [← reverse_involutive w, ← rightWick_vacuum]
    rw [← mul_apply_eq_comp, (commute_rightWick A ((mem_algebra_iff A).mp hA) (reverse w)).eq,
      mul_apply_eq_comp, h0, map_zero]
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change A (lp.single 2 w z) = 0
  have hz : lp.single 2 w z = z • basis w := by simp [basis, ← lp.single_smul]
  rw [hz, map_smul, hsingle, smul_zero]

 theorem adjoint_vacuum_coefficient (A : Space B N G →L[ℂ] Space B N G)
    (hA : A ∈ algebra B N G) (w : Word B N G) :
    (star A (basis empty)) w = star ((A (basis empty)) (reverse w)) := by
  have hw : A (basis w) = rightWick (reverse w) (A (basis empty)) := by
    rw [← mul_apply_eq_comp,
      ← (commute_rightWick A ((mem_algebra_iff A).mp hA) (reverse w)).eq,
      mul_apply_eq_comp, rightWick_vacuum, reverse_involutive]
  calc
    (star A (basis empty)) w = inner ℂ (basis w) (star A (basis empty)) := by
      simp [basis, lp.inner_single_left]
    _ = inner ℂ (A (basis w)) (basis empty) := ContinuousLinearMap.adjoint_inner_right A _ _
    _ = inner ℂ (rightWick (reverse w) (A (basis empty))) (basis empty) := by rw [hw]
    _ = inner ℂ (A (basis empty)) (star (rightWick (reverse w)) (basis empty)) :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = star ((A (basis empty)) (reverse w)) := by
      rw [adjoint_rightWick_vacuum]
      simp [basis, lp.inner_single_right]

 theorem vacuum_product_formula (A D : Space B N G →L[ℂ] Space B N G)
    (hA : A ∈ algebra B N G) :
    inner ℂ (basis empty) ((A * D) (basis empty)) =
      ∑' w : Word B N G, (D (basis empty)) w * (A (basis empty)) (reverse w) := by
  rw [mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left A,
    ← ContinuousLinearMap.star_eq_adjoint, lp.inner_eq_tsum]
  apply tsum_congr
  intro w
  rw [RCLike.inner_apply, adjoint_vacuum_coefficient A hA w]
  simp

 theorem vacuum_tracial (A : Space B N G →L[ℂ] Space B N G) (hA : A ∈ algebra B N G)
    (D : Space B N G →L[ℂ] Space B N G) (hD : D ∈ algebra B N G) :
    inner ℂ (basis empty) ((A * D) (basis empty)) =
      inner ℂ (basis empty) ((D * A) (basis empty)) := by
  rw [vacuum_product_formula A D hA, vacuum_product_formula D A hD]
  let e : Word B N G ≃ Word B N G := ⟨reverse, reverse, reverse_involutive, reverse_involutive⟩
  calc
    (∑' w : Word B N G, (D (basis empty)) w * (A (basis empty)) (reverse w)) =
        ∑' w : Word B N G, (D (basis empty)) (reverse w) * (A (basis empty)) w := by
      simpa [e] using (e.tsum_eq (fun w : Word B N G =>
        (D (basis empty)) w * (A (basis empty)) (reverse w))).symm
    _ = _ := tsum_congr fun _ => mul_comm _ _

def tracialVector (B N G : Type) [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] :
    TracialVector (algebra B N G) where
  vacuum := basis empty
  norm_vacuum := by simp [basis, lp.norm_single (E := fun _ : Word B N G => ℂ) (p := 2)]
  tracial := vacuum_tracial
  separating := vacuum_separating

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

def backgroundAlgebra (J : Set N) : Subalgebra ℂ (Space B N G →L[ℂ] Space B N G) :=
  Algebra.adjoin ℂ (Set.range semicircularB ∪ Set.range unitaryG ∪ semicircularN '' J)

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixChartInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
 def matrixCoordinatesOfHermitian {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) : MatrixCoordinates n d :=
  WithLp.toLp 2 (fun (i,j,k) => if j=k then (A i j j).re else if j<k then Real.sqrt 2*(A i j k).re else Real.sqrt 2*(A i k j).im)
 theorem hermitianMatrix_coordinatesOfHermitian {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i,(A i).IsHermitian) (i : Fin n) :
    hermitianMatrix (matrixCoordinatesOfHermitian A) i = A i := by
  have hs : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  ext j k
  have he := congrFun (congrFun (hA i) j) k
  change conj (A i k j)=A i j k at he
  by_cases hjk:j=k
  · subst k
    have hi := congrArg Complex.im he
    simp only [Complex.conj_im] at hi
    have heq : (A i j j).im=0 := by linarith
    simp only [hermitianMatrix,matrixCoordinatesOfHermitian,PiLp.toLp_apply,ite_true]
    exact Complex.ext (by simp) (by simp [heq])
  · have hkj := Ne.symm hjk
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · simp only [hermitianMatrix,matrixCoordinatesOfHermitian,PiLp.toLp_apply,hjk,hkj,hlt,not_lt_of_gt hlt,ite_false,ite_true,Complex.ofReal_mul]
      rw [div_eq_iff hs]
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
    · simp only [hermitianMatrix,matrixCoordinatesOfHermitian,PiLp.toLp_apply,hjk,hkj,hgt,not_lt_of_gt hgt,ite_false,ite_true,Complex.ofReal_mul]
      rw [div_eq_iff hs,← he]
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixHilbertSchmidt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate Matrix.Norms.L2Operator
open Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def hsVector (A : Matrix (Fin d) (Fin d) ℂ) : EuclideanSpace ℂ (Fin d×Fin d) :=
    WithLp.toLp 2 (fun q => A q.1 q.2)
 theorem hermitianChart_injective : Function.Injective (hermitianChart n d) := by
  intro a b hab
  have he : hermitianChart n d (a-b)=0 := by rw [map_sub,hab,sub_self]
  have hz := hermitianChart_normSq (a-b)
  have hh : ∀i,hermitianMatrix (a-b) i=0 := congrFun he
  simp only [hh,Matrix.zero_apply,map_zero,sum_const_zero] at hz
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (a-b)]))
 def rotateCoordinates (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (a : MatrixCoordinates n d) : MatrixCoordinates n d :=
    matrixCoordinatesOfHermitian (fun i => star (U:Matrix (Fin d) (Fin d) ℂ)*hermitianMatrix a i*U)
 theorem conjugate_hermitian (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) : (star (U:Matrix (Fin d) (Fin d) ℂ)*A*U).IsHermitian := by
  change star _ = _
  simp only [star_mul,star_star]
  rw [show star A=A from hA]
  simp only [mul_assoc]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralBlockMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset MeasureTheory ProbabilityTheory
namespace FiniteEntropySeparation
variable {p d : ℕ}
 def blockMask (f : Fin d → Fin p) : Finset (Fin (p+1) × Fin d × Fin d) :=
    univ.filter (fun q => q.1.val<p ∧ f q.2.1=f q.2.2)
 def balancedBlocks (f : Fin d → Fin p) : Prop :=
    ∀l, p*(univ.filter (fun j => f j=l)).card≤2*d
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.BlockEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped Matrix.Norms.L2Operator ENNReal
namespace FiniteEntropySeparation
variable {p d n : ℕ}
 def blockEvent (p d : ℕ) (r M : ℝ) : Set (MatrixCoordinates (p+1) d) :=
    {a | ‖a‖≤M ∧ ∃f : Fin d → Fin p,balancedBlocks f ∧
      ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖}
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MicrostatesSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology
namespace FiniteEntropySeparation
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 def diagonalMicrostates (R : ℝ) (k d : ℕ) : Set (MatrixCoordinates n d) :=
    microstates τ X R k d ((k+1:ℝ)⁻¹)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianLinearTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped NNReal
open MeasureTheory ProbabilityTheory Finset Set
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 def gaussianLinear (c : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, c i*x i
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEOperatorTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set Metric
namespace FiniteEntropySeparation
 def gueMatrix {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  ((Real.sqrt d : ℂ)⁻¹) • coordinateMatrix x i
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate Classical
open Finset
namespace FiniteEntropySeparation
 variable {α : Type u1} {n d : ℕ}
 def jointMatrix (A : α → Matrix (Fin d) (Fin d) ℂ) (x : MatrixIndex n d → ℝ) : α ⊕ Fin n → Matrix (Fin d) (Fin d) ℂ := Sum.elim A (gueMatrix x)
 def matrixTraceWord (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) : ℂ := (d:ℂ)⁻¹ * Matrix.trace (matrixWord A w)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
namespace FiniteEntropySeparation
 def gaussianMomentMajorant (m : ℕ) : ℝ :=
    (4*Real.exp 64)*(m+1)*∫ t : ℝ in Ioi 0, t^m*Real.exp (-t^2/64)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUELimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
 variable {α : Type u8} {n : ℕ} {D : ℕ → ℕ}
 def expectedMatrixWord (A : (k : ℕ) → α → Matrix (Fin (D k)) (Fin (D k)) ℂ) (k : ℕ) (w : List (α ⊕ Fin n)) : ℂ :=
   ∫ x, matrixTraceWord (jointMatrix (A k) x) w ∂productGaussian (MatrixIndex n (D k))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WordSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1}
abbrev Series (α : Type u2) := List α → ℂ

def unit : Series α
  | [] => 1
  | _::_ => 0

def deriv (a : α) (f : Series α) : Series α := fun w => f (a::w)

def conv (f g : Series α) : Series α
  | [] => f [] * g []
  | a::w => f [] * g (a::w) + conv (deriv a f) g w

@[simp] theorem unit_nil : (unit : Series α) [] = 1 := rfl
@[simp] theorem unit_cons (a : α) (w : List α) : unit (a::w) = 0 := rfl
@[simp] theorem conv_nil (f g : Series α) : conv f g [] = f [] * g [] := rfl
@[simp] theorem conv_cons (f g : Series α) (a : α) (w : List α) :
    conv f g (a::w) = f [] * g (a::w) + conv (deriv a f) g w := rfl
@[simp] theorem deriv_apply (a : α) (f : Series α) (w : List α) : deriv a f w = f (a::w) := rfl

@[simp] theorem deriv_unit (a : α) : deriv a (unit : Series α) = 0 := rfl

@[simp] theorem conv_unit_right (f : Series α) : conv f unit = f := by
  funext w
  induction w generalizing f with
  | nil => simp
  | cons a w ih => simp [ih]

 def Agree (n : ℕ) (f g : Series α) : Prop := ∀ w, w.length ≤ n → f w = g w

def subst (M f : Series α) : Series α
  | [] => f []
  | a::w => ∑ k ∈ range (w.length+1), M (w.take k) * subst M (deriv a f) (w.drop k)
termination_by w => w.length

@[simp] theorem subst_nil (M f : Series α) : subst M f [] = f [] := by rw [subst]

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CumulantSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1}

def inverse (f : Series α) : Series α
  | [] => 1
  | a::w => - ∑ k ∈ range (w.length+1), f (a::w.take k) * inverse f (w.drop k)
termination_by w => w.length

@[simp] theorem inverse_nil (f : Series α) : inverse f [] = 1 := by rw [inverse]

def momentIter (R : Series α) : ℕ → Series α
  | 0 => unit
  | n+1 => unit + subst (momentIter R n) R

@[simp] theorem momentIter_nil {R : Series α} (hR : R [] = 0) (n : ℕ) :
    momentIter R n [] = 1 := by
  cases n <;> simp [momentIter, hR]

 def moments (R : Series α) : Series α := fun w => momentIter R w.length w
@[simp] theorem moments_nil (R : Series α) : moments R [] = 1 := rfl

def boolean (M : Series α) : Series α := unit - inverse M
 def cumulants (M : Series α) : Series α := inverse (moments (-boolean M)) - unit

@[simp] theorem boolean_nil (M : Series α) : boolean M [] = 0 := by simp [boolean]
@[simp] theorem cumulants_nil (M : Series α) : cumulants M [] = 0 := by simp [cumulants]

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SeriesNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1} [Fintype α]

abbrev DegreeSpace (α : Type u2) [Fintype α] (n : ℕ) := EuclideanSpace ℂ (List.Vector α n)
def degreeVector (f : Series α) (n : ℕ) : DegreeSpace α n := WithLp.toLp 2 (fun w => f w.val)
def degreeNorm (f : Series α) (n : ℕ) : ℝ := ‖degreeVector f n‖

@[simp] theorem degreeVector_apply (f : Series α) (n : ℕ) (w : List.Vector α n) :
    degreeVector f n w = f w.val := rfl
@[simp] theorem degreeNorm_nonneg (f : Series α) (n : ℕ) : 0 ≤ degreeNorm f n := norm_nonneg _
@[simp] theorem degreeNorm_zero (n : ℕ) : degreeNorm (0 : Series α) n = 0 := norm_zero

 def vectorSplit (m n : ℕ) : List.Vector α (m+n) ≃ List.Vector α m × List.Vector α n where
  toFun w := (⟨w.val.take m, by simp [w.prop]⟩, ⟨w.val.drop m, by simp [w.prop]⟩)
  invFun v := ⟨v.1.val ++ v.2.val, by simp [v.1.prop, v.2.prop]⟩
  left_inv w := by apply Subtype.ext; exact List.take_append_drop _ _
  right_inv v := by
    apply Prod.ext <;> apply Subtype.ext
    · exact List.take_left' v.1.prop
    · exact List.drop_left' v.1.prop

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.VectorSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev VSeries (α E : Type) := List α → E
abbrev VDegreeSpace (α E : Type) [Fintype α] [NormedAddCommGroup E] (n : ℕ) :=
  PiLp 2 (fun _ : List.Vector α n => E)
def vdegreeVector (f : VSeries α E) (n : ℕ) : VDegreeSpace α E n :=
  WithLp.toLp 2 (fun w => f w.val)
def vdegreeNorm (f : VSeries α E) (n : ℕ) : ℝ := ‖vdegreeVector f n‖
@[simp] theorem vdegreeVector_apply {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (f : VSeries α E) (n : ℕ) (w : List.Vector α n) :
    vdegreeVector f n w = f w.val := rfl
@[simp] theorem vdegreeNorm_nonneg {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (f : VSeries α E) (n : ℕ) : 0 ≤ vdegreeNorm f n := norm_nonneg _
@[simp] theorem vdegreeNorm_zero {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (n : ℕ) : vdegreeNorm (0 : VSeries α E) n = 0 := norm_zero

def vconv (M : Series α) (f : VSeries α E) : VSeries α E := fun w =>
  ∑ k ∈ range (w.length+1), M (w.take k) • f (w.drop k)

 def vsubst (M : Series α) (f : VSeries α E) : VSeries α E
  | [] => f []
  | a::w => ∑ k ∈ range (w.length+1), M (w.take k) • vsubst M (fun v => f (a::v)) (w.drop k)
termination_by w => w.length
@[simp] theorem vsubst_nil {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (M : Series α) (f : VSeries α E) : vsubst M f [] = f [] := by rw [vsubst]

 def bundleDeriv (f : VSeries α E) : VSeries α (PiLp 2 (fun _ : α => E)) := fun w =>
  WithLp.toLp 2 (fun a => f (a::w))
@[simp] theorem bundleDeriv_apply {α E : Type} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℂ E] (f : VSeries α E) (w : List α) (a : α) :
    bundleDeriv f w a = f (a::w) := rfl

def vectorCons (n : ℕ) : α × List.Vector α n ≃ List.Vector α (n+1) where
  toFun v := v.1 ::ᵥ v.2
  invFun w := (w.head,w.tail)
  left_inv v := by simp
  right_inv w := w.cons_head_tail

def substBound (b a : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | n+1 => ∑ k ∈ range (n+1), b k * substBound b (fun j => a (j+1)) (n-k)
termination_by n => n

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SeriesWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset

 def truncEval (a : ℕ → ℝ) (r : ℝ) (N : ℕ) : ℝ := ∑ n ∈ range (N+1), r^n * a n
@[simp] theorem truncEval_zero (a : ℕ → ℝ) (r : ℝ) : truncEval a r 0 = a 0 := by simp [truncEval]

 def scalarConv (a b : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ range (n+1), a k * b (n-k)

variable {α : Type} [Fintype α]
 def seriesWeight (f : Series α) (r : ℝ) (N : ℕ) : ℝ := truncEval (degreeNorm f) r N

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SeriesAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [Fintype α]

@[simp] theorem degreeNorm_neg (f : Series α) (n : ℕ) : degreeNorm (-f) n = degreeNorm f n := by
  change ‖-degreeVector f n‖ = _
  exact norm_neg _
@[simp] theorem seriesWeight_neg (f : Series α) (r : ℝ) (N : ℕ) :
    seriesWeight (-f) r N = seriesWeight f r N := by simp [seriesWeight, truncEval]

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SemicircularSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α]

def letter (i : α) : Series α
  | [j] => if j=i then 1 else 0
  | _ => 0
def quadratic : Series α
  | [i,j] => if j=i then 1 else 0
  | _ => 0
@[simp] theorem letter_nil (i : α) : letter i [] = 0 := rfl
@[simp] theorem quadratic_nil : (quadratic : Series α) [] = 0 := rfl

def fockMoments (p : ℕ) : Series (Fin p) := wordMoment (Fock.tracialVector (Fin p)) Fock.semicircular

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CyclicSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α] [Fintype α]

def rightDeriv (i : α) (f : Series α) : Series α := fun w => f (w ++ [i])
def Cyclic (f : Series α) : Prop := ∀ i, deriv i f = rightDeriv i f
@[simp] theorem rightDeriv_apply {α : Type} [DecidableEq α] [Fintype α] (i : α) (f : Series α) (w : List α) :
    rightDeriv i f w = f (w ++ [i]) := rfl
@[simp] theorem rightDeriv_unit {α : Type} [DecidableEq α] [Fintype α] (i : α) : rightDeriv i (unit : Series α) = 0 := by
  funext w
  cases w <;> rfl
@[simp] theorem rightDeriv_zero {α : Type} [DecidableEq α] [Fintype α] (i : α) : rightDeriv i (0 : Series α) = 0 := rfl

def rightAssemble (f : α → Series α) : Series α := ∑ i, conv (f i) (letter i)
@[simp] theorem rightAssemble_nil (f : α → Series α) : rightAssemble f [] = 0 := by
  simp [rightAssemble]

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.LinearSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β γ : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

def reparam (c : α → β → ℂ) (f : Series α) : Series β
  | [] => f []
  | b::w => ∑ a, c a b * reparam c (deriv a f) w
@[simp] theorem reparam_nil {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) : reparam c f [] = f [] := rfl

def restrict (e : β → α) (f : Series α) : Series β := fun w => f (w.map e)
end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EmbeddedSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β γ : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

def liftSeries (e : α → β) : Series α → Series β := reparam (fun a b => if e a=b then 1 else 0)
@[simp] theorem liftSeries_nil {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (e : α → β) (f : Series α) : liftSeries e f [] = f [] := rfl

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Signal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

namespace FreeTensor

variable {B N A : Type} [DecidableEq B] [DecidableEq N] [AddCommGroup A]
  [Fintype A] [DecidableEq A]

abbrev groupUnitary (a : A) : Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A) :=
  unitaryG (Multiplicative.ofAdd a)

omit [Fintype A] in
@[simp] theorem groupUnitary_zero : groupUnitary (B := B) (N := N) (0 : A) = 1 :=
  unitaryG_one

omit [Fintype A] in
@[simp] theorem star_groupUnitary (a : A) :
    star (groupUnitary (B := B) (N := N) a) = groupUnitary (-a) := star_unitaryG _

def characterProjection (ψ : AddChar A ℂ) :
    Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A) :=
  (Fintype.card A : ℂ)⁻¹ • ∑ a : A, ψ (-a) • groupUnitary a

@[simp] theorem star_characterProjection (ψ : AddChar A ℂ) :
    star (characterProjection (B := B) (N := N) ψ) = characterProjection ψ := by
  unfold characterProjection
  simp only [star_smul, star_inv₀, star_natCast,
    star_sum (R := Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A)),
    star_groupUnitary]
  congr 1
  apply Fintype.sum_equiv (Equiv.neg A)
  intro a
  simp only [Equiv.neg_apply, neg_neg]
  congr 1
  rw [AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj]
  simp

def spectralSignal (y : AddChar A ℂ → ℝ) :
    Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A) :=
  ∑ ψ, (y ψ : ℂ) • characterProjection ψ

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace LabelHilbert
variable {α β : Type} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
 theorem orthogonal_embedding (f : α → β) (hf : Function.Injective f) :
    OrthogonalFamily ℂ (fun _ : α => ℂ) (fun a => coordinateIsometry (f a)) := by
  intro a b hab x y
  change inner ℂ (lp.single (E := fun _ : β => ℂ) 2 (f a) x)
    (lp.single (E := fun _ : β => ℂ) 2 (f b) y) = 0
  rw [lp.inner_single_left, lp.single_apply_ne (E := fun _ : β => ℂ) 2 (f b) y
    (fun h => hab (hf h))]
  simp

 def embedding (f : α → β) (hf : Function.Injective f) : Space α →ₗᵢ[ℂ] Space β :=
  (orthogonal_embedding f hf).linearIsometry

@[simp] theorem embedding_single (f : α → β) (hf : Function.Injective f) (a : α) (z : ℂ) :
    embedding f hf (lp.single 2 a z) = lp.single 2 (f a) z :=
  (orthogonal_embedding f hf).linearIsometry_apply_single z

end LabelHilbert
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

def signalSlice (g : G) : Fock.Space B →L[ℂ] Space B N G :=
  (LabelHilbert.embedding (fun w : List B => ((w,g), ([] : List (N × Atom B G))))
    (by intro v w h; exact congrArg (fun a => a.1.1) h)).toContinuousLinearMap

omit [Group G] in
@[simp] theorem signalSlice_single (g : G) (v : List B) (z : ℂ) :
    signalSlice (N := N) g (lp.single 2 v z) = lp.single 2 ((v,g),[]) z := by
  exact LabelHilbert.embedding_single
    (fun w : List B => ((w,g), ([] : List (N × Atom B G))))
    (by intro v w h; exact congrArg (fun a => a.1.1) h) v z

omit [Group G] in
@[simp] theorem signalSlice_basis [Group G] (g : G) (v : List B) :
    signalSlice (N := N) g (Fock.basisVector v) = basis ((v,g),[]) :=
  signalSlice_single g v 1

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.NoiseTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G]

def noiseWord : List N → Word B N G
  | [] => empty
  | i :: w => leftN i (noiseWord w)

@[simp] theorem noiseWord_nil : noiseWord ([] : List N) = (empty : Word B N G) := rfl
@[simp] theorem noiseWord_cons (i : N) (w : List N) :
    noiseWord (i :: w) = (leftN i (noiseWord w) : Word B N G) := rfl

 theorem noiseWord_formula (w : List N) :
    noiseWord (B := B) (G := G) w = (([],1), w.map (fun i => (i,([],1)))) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [noiseWord, ih, leftN, push]

 theorem noiseWord_injective : Function.Injective (noiseWord (B := B) (N := N) (G := G)) := by
  intro v w h
  have h' := congrArg (fun a : Word B N G => a.2.map Prod.fst) h
  simpa [noiseWord_formula, List.map_map, Function.comp_def] using h'

@[simp] theorem rightN_noiseWord (i : N) (w : List N) :
    rightN i (noiseWord (B := B) (G := G) w) = noiseWord (w ++ [i]) := by
  simp [rightN_eq_append, append, noiseWord_formula]

variable [DecidableEq B] [DecidableEq N] [DecidableEq G]

def noiseSlice : Fock.Space N →L[ℂ] Space B N G :=
  (LabelHilbert.embedding noiseWord noiseWord_injective).toContinuousLinearMap

@[simp] theorem noiseSlice_single (w : List N) (z : ℂ) :
    noiseSlice (B := B) (G := G) (lp.single 2 w z) = lp.single 2 (noiseWord w) z :=
  LabelHilbert.embedding_single noiseWord noiseWord_injective w z

@[simp] theorem noiseSlice_basis (w : List N) :
    noiseSlice (B := B) (G := G) (Fock.basisVector w) = basis (noiseWord w) :=
  noiseSlice_single w 1

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorConcat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G]

def atomMul (a b : Atom B G) : Atom B G := (a.1 ++ b.1, a.2 * b.2)

def concatAux (a : Atom B G) : List (N × Atom B G) → Word B N G → Word B N G
  | [], v => (atomMul a v.1, v.2)
  | (i,b) :: t, v => push a i (concatAux b t v)

def concat (w v : Word B N G) : Word B N G := concatAux w.1 w.2 v

@[simp] theorem concat_nil (a : Atom B G) (v : Word B N G) :
    concat (a, ([] : List (N × Atom B G))) v = (atomMul a v.1, v.2) := rfl

@[simp] theorem concat_push (a : Atom B G) (i : N) (w v : Word B N G) :
    concat (push a i w) v = push a i (concat w v) := rfl

@[simp] theorem concat_empty_left (v : Word B N G) : concat empty v = v := by
  rcases v with ⟨⟨l,g⟩,t⟩
  simp [concat, concatAux, empty, atomMul]

@[simp] theorem concat_empty_right (w : Word B N G) : concat w empty = w := by
  rcases w with ⟨a,t⟩
  induction t generalizing a with
  | nil => simp [concat, concatAux, empty, atomMul]
  | cons p t ih =>
    rcases p with ⟨i,b⟩
    change push a i (concat (b,t) empty) = _
    rw [ih]
    rfl

 theorem concat_tail_length (w v : Word B N G) :
    (concat w v).2.length = w.2.length + v.2.length := by
  rcases w with ⟨a,t⟩
  induction t generalizing a with
  | nil => simp [concat, concatAux]
  | cons p t ih =>
    rcases p with ⟨i,b⟩
    change (push a i (concat (b,t) v)).2.length = _
    simp only [push, List.length_cons, ih]
    omega

 theorem atomMul_right_injective (b : Atom B G) : Function.Injective (fun a => atomMul a b) := by
  rintro ⟨v,g⟩ ⟨w,h⟩ he
  simpa [atomMul] using he

 theorem concat_right_injective (v : Word B N G) : Function.Injective (fun w => concat w v) := by
  rintro ⟨a,t⟩ ⟨b,s⟩ h
  have hl : t.length = s.length := by
    have hh := congrArg (fun w : Word B N G => w.2.length) h
    simp only [concat_tail_length] at hh
    omega
  induction t generalizing a b s with
  | nil =>
    have hs : s = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    subst s
    have he : atomMul a v.1 = atomMul b v.1 := congrArg Prod.fst h
    exact congrArg (fun a => (a, ([] : List (N × Atom B G)))) (atomMul_right_injective _ he)
  | cons p t ih =>
    cases s with
    | nil => simp at hl
    | cons q s =>
      rcases p with ⟨i,c⟩
      rcases q with ⟨j,d⟩
      have he : a = b ∧ i = j ∧ concat (c,t) v = concat (d,s) v := by
        have he := h
        simp only [concat, concatAux, push, Prod.mk.injEq, List.cons.injEq, and_assoc] at he
        exact ⟨he.1, he.2.1, Prod.ext he.2.2.1 he.2.2.2⟩
      rcases he with ⟨rfl,rfl,he⟩
      have hh := ih c d s he (by simpa using hl)
      cases hh
      rfl

variable [DecidableEq B] [DecidableEq N] [DecidableEq G]

def suffixEmbedding (v : Word B N G) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (fun w => concat w v) (concat_right_injective v)

@[simp] theorem suffixEmbedding_single (v w : Word B N G) (z : ℂ) :
    suffixEmbedding v (lp.single 2 w z) = lp.single 2 (concat w v) z :=
  LabelHilbert.lift_single _ _ _ _

@[simp] theorem suffixEmbedding_basis (v w : Word B N G) :
    suffixEmbedding v (basis w) = basis (concat w v) := suffixEmbedding_single v w 1

def StartsNoise (i : N) (w : Word B N G) : Prop :=
  ∃ v, w = leftN i v

def Supported (J : Set N) (w : Word B N G) : Prop :=
  ∀ p ∈ w.2, p.1 ∈ J

def StartsBackground (J : Set N) (w : Word B N G) : Prop :=
  w.1 ≠ ([],1) ∨ ∃ i ∈ J, StartsNoise i w

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorFreeness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

def labelSpace (P : Word B N G → Prop) : Submodule ℂ (Space B N G) :=
  Submodule.span ℂ {x | ∃ w, P w ∧ x = basis w}

def PureSupported (J : Set N) (w : Word B N G) : Prop :=
  ∃ l : List N, (∀ i ∈ l, i ∈ J) ∧ w = noiseWord l

def StartsNoiseIn (J : Set N) (w : Word B N G) : Prop :=
  ∃ i ∈ J, StartsNoise i w

def noiseAlgebras {κ : Type} (J : Set N) (σ : κ → N) :
    Option κ → Subalgebra ℂ (Space B N G →L[ℂ] Space B N G)
  | none => backgroundAlgebra J
  | some i => Algebra.adjoin ℂ {semicircularN (σ i)}

def StartsColor {κ : Type} (J : Set N) (σ : κ → N) : Option κ → Word B N G → Prop
  | none => StartsBackground J
  | some i => StartsNoise (σ i)

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EquidiscreteSignal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

def equidiscreteAtom (p : ℕ) (l : Fin p) : ℝ := -1 + 2 * l.val / (p - 1 : ℝ)

namespace FreeTensor
variable {B N : Type} [DecidableEq B] [DecidableEq N] (p : ℕ) [NeZero p]

def dualIndex : AddChar (ZMod p) ℂ ≃ Fin p :=
  Fintype.equivFinOfCardEq (by simp)

def equidiscreteSignal : Space B N (Multiplicative (ZMod p)) →L[ℂ] Space B N (Multiplicative (ZMod p)) :=
  spectralSignal (fun ψ => equidiscreteAtom p (dualIndex p ψ))

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.ActualTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
abbrev H := Space (Fin p) (Fin ((p+1)+(p+1))) (Multiplicative (ZMod p))
abbrev M : VonNeumannAlgebra (H p) := algebra (Fin p) (Fin ((p+1)+(p+1))) (Multiplicative (ZMod p))
abbrev τ : TracialVector (M p) := tracialVector _ _ _
def C : Fin (p+1) → H p →L[ℂ] H p :=
  Fin.lastCases (equidiscreteSignal p) (fun i => semicircularB i)
def initialIndex (i : Fin (p+1)) : Fin ((p+1)+(p+1)) := Fin.castAdd (p+1) i
def auxiliaryIndex (i : Fin (p+1)) : Fin ((p+1)+(p+1)) := Fin.natAdd (p+1) i
def initialNoise (i : Fin (p+1)) : H p →L[ℂ] H p := semicircularN (initialIndex p i)
def auxiliaryNoise (i : Fin (p+1)) : H p →L[ℂ] H p := semicircularN (auxiliaryIndex p i)
def oldNoise : Set (Fin ((p+1)+(p+1))) := Set.range (initialIndex p)
def X (h : ℝ) : Fin (p+1) → H p →L[ℂ] H p := heatTuple (C p) (initialNoise p) h

@[simp] theorem C_last : C p (Fin.last p) = equidiscreteSignal p := by simp [C]
@[simp] theorem C_castSucc (i : Fin p) : C p i.castSucc = semicircularB i := by simp [C]

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MixedGaussianSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {n : ℕ}
def leftIndex : Fin n → Fin (n+n) := Fin.castAdd n
def rightIndex : Fin n → Fin (n+n) := Fin.natAdd n
def gaussianJointR (R : Series (Fin n)) : Series (Fin (n+n)) :=
  liftSeries leftIndex R + liftSeries rightIndex quadratic
@[simp] theorem gaussianJointR_nil (R : Series (Fin n)) (hR : R [] = 0) : gaussianJointR R [] = 0 := by
  simp [gaussianJointR, hR]
end FreeSeries

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
def jointTuple (X : Fin n → Space B N G →L[ℂ] Space B N G) (σ : Fin n → N) :
    Fin (n+n) → Space B N G →L[ℂ] Space B N G := Fin.addCases X (fun i => semicircularN (σ i))
@[simp] theorem jointTuple_left (X : Fin n → Space B N G →L[ℂ] Space B N G) (σ : Fin n → N) (i : Fin n) :
    jointTuple X σ (leftIndex i) = X i := Fin.addCases_left i
@[simp] theorem jointTuple_right (X : Fin n → Space B N G →L[ℂ] Space B N G) (σ : Fin n → N) (i : Fin n) :
    jointTuple X σ (rightIndex i) = semicircularN (σ i) := Fin.addCases_right i
end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatCumulants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {n : ℕ}

def heatCoefficients (u : ℝ) (a : Fin (n+n)) (b : Fin n) : ℂ :=
  Fin.addCases (fun i => if i=b then 1 else 0)
    (fun i => if i=b then (Real.sqrt u : ℂ) else 0) a
@[simp] theorem heatCoefficients_left (u : ℝ) (a b : Fin n) :
    heatCoefficients u (leftIndex a) b = if a=b then 1 else 0 := Fin.addCases_left a
@[simp] theorem heatCoefficients_right (u : ℝ) (a b : Fin n) :
    heatCoefficients u (rightIndex a) b = if a=b then (Real.sqrt u : ℂ) else 0 := Fin.addCases_right a
end FreeSeries

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixReparam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
open FreeSeries
 def heatMatrix {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (u : ℝ) (x : MatrixIndex n d → ℝ) : Fin n → Matrix (Fin d) (Fin d) ℂ :=
  fun i => A i+(Real.sqrt u:ℂ) • gueMatrix x i
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEFreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
open FreeSeries
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
def sumJointMoment (X : Fin n → Space B N G →L[ℂ] Space B N G) (σ : Fin n → N)
    (w : List (Fin n ⊕ Fin n)) : ℂ :=
  wordMoment (tracialVector B N G) (jointTuple X σ) (w.map finSumFinEquiv)
end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUESelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped Classical Topology
namespace FiniteEntropySeparation
 def gueBad (n m d : ℕ) (ε : ℝ) : Set (MatrixIndex n d → ℝ) :=
    {x | (∃ i,64 < matrixOpNorm (gueMatrix x i)) ∨ ∃ w : List (Fin n), w.length ≤ m ∧ ε ≤ ‖matrixTraceWord (gueMatrix x) w-FreeSeries.fockMoments n w‖}
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MicrostatesHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped Classical Topology ENNReal
namespace FiniteEntropySeparation
 def heatCoordinates {n d : ℕ} (a : MatrixCoordinates n d) (u : ℝ) (x : MatrixIndex n d → ℝ) : MatrixCoordinates n d :=
  a+(Real.sqrt u/Real.sqrt d) • WithLp.toLp 2 x
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralClustering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
variable {p d : ℕ}
 def badSpectrum (y : Fin p → ℝ) (δ : ℝ) (x : Fin d → ℝ) : Finset (Fin d) :=
    univ.filter (fun j => ∀l,δ < |x j-y l|)
 def clusterLabel [NeZero p] (y : Fin p → ℝ) (δ : ℝ) (x : Fin d → ℝ) (j : Fin d) : Fin p :=
    if h : ∃l,|x j-y l|≤δ then h.choose else 0
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralTestFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter
open scoped Topology ComplexConjugate
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def commutatorMoment (m : List (Fin n) → ℂ) (i j : Fin n) : ℝ :=
    (m [i,j,j,i]-m [i,j,i,j]-m [j,i,j,i]+m [j,i,i,j]).re
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {p : ℕ}
 def badFraction (p : ℕ) : ℝ := min (1/4096:ℝ) (1/(2*p))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.OptionSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β : Type} [DecidableEq α] [Fintype α]

def ignoreLetter (f : Series α) : Series (Option α) := fun w => f (w.filterMap id)

 def vectorMap (e : α ≃ β) (n : ℕ) : List.Vector α n ≃ List.Vector β n where
  toFun w := ⟨w.val.map e, by simp [w.prop]⟩
  invFun w := ⟨w.val.map e.symm, by simp [w.prop]⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp

def optionFin (p : ℕ) : Option (Fin p) ≃ Fin (p+1) where
  toFun := fun a => match a with | none => Fin.last p | some i => i.castSucc
  invFun := Fin.lastCases none some
  left_inv a := by cases a <;> simp
  right_inv a := by induction a using Fin.lastCases <;> simp
@[simp] theorem optionFin_none (p : ℕ) : optionFin p none = Fin.last p := rfl
@[simp] theorem optionFin_some (p : ℕ) (i : Fin p) : optionFin p (some i) = i.castSucc := rfl

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SignalSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
def signalMoments : Series (Fin (p+1)) := wordMoment (τ p) (C p)
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MonomialSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {α : Type} [DecidableEq α]
def monomial (v : List α) : Series α := fun w => if w=v then 1 else 0
@[simp] theorem monomial_nil : monomial ([] : List α) = unit := by
  funext w; cases w <;> simp [monomial, unit]
@[simp] theorem monomial_cons_nil (a : α) (v : List α) : monomial (a::v) [] = 0 := by simp [monomial]

variable [Fintype α]
def wordBall (d : ℕ) : Finset (List α) :=
  (range (d+1)).biUnion (fun m => univ.image (fun v : List.Vector α m => v.val))
@[simp] theorem mem_wordBall (v : List α) (d : ℕ) : v ∈ wordBall d ↔ v.length ≤ d := by
  simp only [wordBall, mem_biUnion, mem_range, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨m,hm,q,rfl⟩; rw [q.prop]; omega
  · intro h; exact ⟨v.length, by omega, ⟨v,rfl⟩, rfl⟩
end FreeSeries

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WickSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 def noiseWickIsometry {n : ℕ} (σ : Fin n → N) (hσ : Function.Injective σ) :
    LabelHilbert.Space (List (Fin n)) →ₗᵢ[ℂ] Space B N G :=
  LabelHilbert.embedding (fun js => noiseWord ((js.map σ).reverse)) (by
    intro js ks h
    apply List.map_injective_iff.mpr hσ
    exact List.reverse_injective (noiseWord_injective h))

@[simp] theorem noiseWickIsometry_single {n : ℕ} (σ : Fin n → N)
    (hσ : Function.Injective σ) (js : List (Fin n)) (z : ℂ) :
    noiseWickIsometry (B := B) (G := G) σ hσ (lp.single 2 js z) =
      z • basis (noiseWord ((js.map σ).reverse)) := by
  have hz : z • (basis (noiseWord ((js.map σ).reverse)) : Space B N G) =
      lp.single 2 (noiseWord ((js.map σ).reverse)) z := by
    simp [basis, ← lp.single_smul]
  rw [hz]
  exact LabelHilbert.embedding_single _ _ js z

 def wickCoefficientVector {n : ℕ} (a : List (Fin n) → ℂ)
    (ha : Summable (fun js => ‖a js‖ ^ 2)) : LabelHilbert.Space (List (Fin n)) :=
  ⟨a, (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr (by simpa using ha)⟩

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CumulantResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {α : Type} [DecidableEq α]
def reverseEquiv : List α ≃ List α where
  toFun := List.reverse
  invFun := List.reverse
  left_inv := List.reverse_reverse
  right_inv := List.reverse_reverse

def residual (R : Series α) (v : α → ℝ) (i : α) : Series α :=
  FreeSeries.deriv i R - (v i : ℂ) • letter i
end FreeSeries

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TwoNoiseFisher
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

 def doublyNoised (h s : ℝ) := heatTuple (X p h) (auxiliaryNoise p) s
 def noiseVector₀ (i : Fin (p+1)) : H p := basis (noiseWord [initialIndex p i])
 def noiseVector₁ (i : Fin (p+1)) : H p := basis (noiseWord [auxiliaryIndex p i])

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SignalCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
def variance (i : Fin (p+1)) : ℝ := ‖C p i (τ p).vacuum‖ ^ 2
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SeriesSummability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [Fintype α]

def wordSigma : (Σ n : ℕ, List.Vector α n) ≃ List α where
  toFun v := v.2.val
  invFun w := ⟨w.length, ⟨w,rfl⟩⟩
  left_inv v := by rcases v with ⟨n,⟨w,hw⟩⟩; cases hw; rfl
  right_inv w := rfl

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WickCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α] [Fintype α]

def vectorReverse (d : ℕ) : List.Vector α d ≃ List.Vector α d where
  toFun v := v.reverse
  invFun v := v.reverse
  left_inv v := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

def wickCoefficients (f : Series α) (u : ℝ) : Series α :=
  fun js => conj (f js.reverse) / (Real.sqrt u : ℂ)^js.length

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GeometricTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset

def geometricCumulantTail (K u : ℝ) (k : ℕ) : ℝ :=
  if 2 ≤ k then u⁻¹^k * K^(2*(k+1)) else 0
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
def cumulantConstant : ℝ := 128*Real.sqrt (Real.sqrt p)
def covarianceFisher (u : ℝ) : ℝ := ∑ i : Fin (p+1), (variance p i + u)⁻¹
def fisherDeficit (u : ℝ) : ℝ := (freeFisher (τ p) (X p u)).toReal - covarianceFisher p u
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.BlockGaussianQuantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
namespace FiniteEntropySeparation
variable {p d : ℕ}
 def chosenP : ℕ := 2^64
 def chosenTime : ℝ := 2^48
 instance chosenP_neZero : NeZero chosenP := ⟨by norm_num [chosenP]⟩
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianDeBruijn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory Filter Set Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
def classicalEntropy (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) : ℝ :=
  -(∫x,smoothedDensity μ s x*Real.log (smoothedDensity μ s x))
def classicalFisher (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) : ℝ :=
  ∑i,∫x,(smoothedGradient μ s x i)^2/smoothedDensity μ s x
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianEntropyEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open MeasureTheory Set Classical
namespace FiniteEntropySeparation
 def eventTilt {Ω : Type u2} (g : Ω → ℝ) (E : Set Ω) (z : ℝ) (x : Ω) : ℝ :=
  (if x∈E then Real.exp z else 1)/2*g x
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Finset
namespace FiniteEntropySeparation
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
def heatFisherReal (u : ℝ) : ℝ := (freeFisher (τ p) (X p u)).toReal
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EntropyReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Finset
namespace FiniteEntropySeparation

namespace Model
variable (p : ℕ) [NeZero p]
def gaussianEntropy (a : ℝ) : ℝ :=
  (p+1 : ℕ)/2 * Real.log (2*Real.pi*Real.exp 1) +
    (1/2 : ℝ) * ∑ i : Fin (p+1), Real.log (a + variance p i)
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FlowSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 def chosenStart (h : ℝ) : ℝ := h/(4*((chosenP+1:ℕ):ℝ))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
 def blockVector {d p : ℕ} (v : EuclideanSpace ℂ (Fin (d*p))) (l : Fin p) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun j => v (finProdFinEquiv (j,l)))
end FiniteEntropySeparation

end

end OAI
end


