-- Prove2me | Definitions.Def_ApproxDegCompV1_OperatorReadout
-- name    : ApproxDegCompV1_OperatorReadout
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-13T04:14:05.247733+00:00
-- url     : https://prove2.me/theorems/ebe0c418-3bd2-44fc-9dc1-e2e4182e6d0d
-- title:
--   Approximate-degree composition: Local polynomial operators and output-count grading
-- statement:
--   This module formalizes local polynomial operators and output-count grading for the Lean proof of the approximate-degree composition lower bound.
-- source:
--   https://prove2.me/theorems/f8385c32-068c-45a1-99ed-f7cf0a99f266

import Definitions.Def_ApproxDegCompV1_FourierExtraction
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Permutation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

-- PhaseHilbertBridge.lean
section
/-!
# The algebraic phase functional in the actual Hilbert norm

On the unit circle the reciprocal bra is the true adjoint ket. We identify
the exact functional and derive its operator-norm bound, including rectangular
isometric compression. No default Matrix norm is used.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace ApproxDegree.PhaseHilbertBridge

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def phaseVector (z : ι → ℂ) (t : ℂ) : EuclideanSpace ℂ (TensorPhase.Bits ι) :=
  WithLp.toLp 2 (TensorPhase.phaseKet z t)

theorem sign_conj {z : ℂ} (hz : z * z = 1) : conj z = z := by
  rcases mul_self_eq_one_iff.mp hz with rfl | rfl <;> simp

theorem sign_norm {z : ℂ} (hz : z * z = 1) : ‖z‖ = 1 := by
  rcases mul_self_eq_one_iff.mp hz with rfl | rfl <;> simp

omit [DecidableEq ι] in
theorem phaseBra_eq_conj (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (t : ℂ) (ht : ‖t‖ = 1) (a : TensorPhase.Bits ι) :
    TensorPhase.phaseBra z t a = conj (TensorPhase.phaseKet z t a) := by
  unfold TensorPhase.phaseBra TensorPhase.phaseKet
  rw [map_prod]
  apply prod_congr rfl
  intro i hi
  cases a i <;> simp [TensorPhase.localBra, TensorPhase.localKet,
    Complex.inv_eq_conj ht, sign_conj (hz i)]

omit [DecidableEq ι] in
theorem phaseKet_norm (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (t : ℂ) (ht : ‖t‖ = 1) (a : TensorPhase.Bits ι) :
    ‖TensorPhase.phaseKet z t a‖ = 1 := by
  unfold TensorPhase.phaseKet
  rw [Complex.norm_prod]
  apply prod_eq_one
  intro i hi
  cases a i <;> simp [TensorPhase.localKet, sign_norm (hz i), ht]

theorem phaseVector_norm_sq (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (t : ℂ) (ht : ‖t‖ = 1) :
    ‖phaseVector z t‖ ^ 2 = (2 : ℝ) ^ Fintype.card ι := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [phaseVector, phaseKet_norm z hz t ht, TensorPhase.Bits]

theorem phaseExpectation_eq_inner (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (t : ℂ) (ht : ‖t‖ = 1) (B : Matrix (TensorPhase.Bits ι) (TensorPhase.Bits ι) ℂ) :
    TensorPhase.phaseExpectation z t B =
      (((2 : ℝ) ^ Fintype.card ι)⁻¹ : ℂ) *
        inner ℂ (phaseVector z t) (B.toEuclideanLin (phaseVector z t)) := by
  have hi : inner ℂ (phaseVector z t) (B.toEuclideanLin (phaseVector z t)) =
      ∑ a, ∑ b, TensorPhase.phaseBra z t a * B a b * TensorPhase.phaseKet z t b := by
    rw [PiLp.inner_apply]
    apply sum_congr rfl
    intro a ha
    change (∑ b, B a b * TensorPhase.phaseKet z t b) *
      conj (TensorPhase.phaseKet z t a) = _
    rw [sum_mul]
    apply sum_congr rfl
    intro b hb
    rw [phaseBra_eq_conj z hz t ht a]
    ring
  rw [hi]
  rfl

/-- The normalized phase functional is bounded by the genuine Hilbert operator
norm of its matrix argument. -/
theorem norm_phaseExpectation_le (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (t : ℂ) (ht : ‖t‖ = 1) (B : Matrix (TensorPhase.Bits ι) (TensorPhase.Bits ι) ℂ) :
    ‖TensorPhase.phaseExpectation z t B‖ ≤ ‖HilbertPointBridge.matrixOperator B‖ := by
  let c : ℝ := ((2 : ℝ) ^ Fintype.card ι)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hn : c * ‖phaseVector z t‖ ^ 2 = 1 := by
    rw [phaseVector_norm_sq z hz t ht]
    exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
  have hi := norm_inner_le_norm (𝕜 := ℂ) (phaseVector z t) (B.toEuclideanLin (phaseVector z t))
  have hb := (HilbertPointBridge.matrixOperator B).le_opNorm (phaseVector z t)
  have hcn : ‖(((2 : ℝ) ^ Fintype.card ι)⁻¹ : ℂ)‖ = c := by simp [c]
  rw [phaseExpectation_eq_inner z hz t ht B, norm_mul, hcn]
  change c * ‖inner ℂ (phaseVector z t) (B.toEuclideanLin (phaseVector z t))‖ ≤ _
  calc
    c * ‖inner ℂ (phaseVector z t) (B.toEuclideanLin (phaseVector z t))‖ ≤
        c * (‖phaseVector z t‖ * (‖HilbertPointBridge.matrixOperator B‖ * ‖phaseVector z t‖)) := by
      exact mul_le_mul_of_nonneg_left
        (hi.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))) hc
    _ = (c * ‖phaseVector z t‖ ^ 2) * ‖HilbertPointBridge.matrixOperator B‖ := by ring
    _ = ‖HilbertPointBridge.matrixOperator B‖ := by rw [hn, one_mul]

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

theorem compression_inner (V : Matrix Y (TensorPhase.Bits ι) ℂ) (R : Matrix Y Y ℂ)
    (v : EuclideanSpace ℂ (TensorPhase.Bits ι)) :
    inner ℂ v ((V.conjTranspose * R * V).toEuclideanLin v) =
      inner ℂ (V.toEuclideanLin v) (R.toEuclideanLin (V.toEuclideanLin v)) := by
  rw [Matrix.toLpLin_mul 2 2 2, LinearMap.comp_apply,
    Matrix.toLpLin_mul 2 2 2, LinearMap.comp_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right _ _ _

theorem gram_identity_norm (V : Matrix Y (TensorPhase.Bits ι) ℂ)
    (hgram : V.conjTranspose * V = 1) (v : EuclideanSpace ℂ (TensorPhase.Bits ι)) :
    ‖V.toEuclideanLin v‖ = ‖v‖ := by
  have hi := compression_inner V (1 : Matrix Y Y ℂ) v
  have he : inner ℂ v v = inner ℂ (V.toEuclideanLin v) (V.toEuclideanLin v) := by
    simpa only [Matrix.mul_one, hgram, Matrix.toLpLin_one, LinearMap.id_apply] using hi
  have hs : ‖v‖ ^ 2 = ‖V.toEuclideanLin v‖ ^ 2 := by
    calc
      ‖v‖ ^ 2 = (inner ℂ v v).re := (inner_self_eq_norm_sq (𝕜 := ℂ) v).symm
      _ = (inner ℂ (V.toEuclideanLin v) (V.toEuclideanLin v)).re := congrArg Complex.re he
      _ = ‖V.toEuclideanLin v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  nlinarith [norm_nonneg v, norm_nonneg (V.toEuclideanLin v)]

/-- An actual rectangular isometry preserves the phase-sample norm bound. -/
theorem norm_compressed_phaseExpectation_le
    (V : Matrix Y (TensorPhase.Bits ι) ℂ) (hgram : V.conjTranspose * V = 1)
    (R : Matrix Y Y ℂ) (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (t : ℂ) (ht : ‖t‖ = 1) :
    ‖TensorPhase.phaseExpectation z t (V.conjTranspose * R * V)‖ ≤
      ‖HilbertPointBridge.matrixOperator R‖ := by
  let c : ℝ := ((2 : ℝ) ^ Fintype.card ι)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hn : c * ‖V.toEuclideanLin (phaseVector z t)‖ ^ 2 = 1 := by
    rw [gram_identity_norm V hgram, phaseVector_norm_sq z hz t ht]
    exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
  have hi := norm_inner_le_norm (𝕜 := ℂ) (V.toEuclideanLin (phaseVector z t))
    (R.toEuclideanLin (V.toEuclideanLin (phaseVector z t)))
  have hb := (HilbertPointBridge.matrixOperator R).le_opNorm (V.toEuclideanLin (phaseVector z t))
  have hcn : ‖(((2 : ℝ) ^ Fintype.card ι)⁻¹ : ℂ)‖ = c := by simp [c]
  rw [phaseExpectation_eq_inner z hz t ht, compression_inner, norm_mul, hcn]
  change c * ‖inner ℂ (V.toEuclideanLin (phaseVector z t))
    (R.toEuclideanLin (V.toEuclideanLin (phaseVector z t)))‖ ≤ _
  calc
    _ ≤ c * (‖V.toEuclideanLin (phaseVector z t)‖ *
        (‖HilbertPointBridge.matrixOperator R‖ * ‖V.toEuclideanLin (phaseVector z t)‖)) :=
      mul_le_mul_of_nonneg_left
        (hi.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))) hc
    _ = (c * ‖V.toEuclideanLin (phaseVector z t)‖ ^ 2) *
        ‖HilbertPointBridge.matrixOperator R‖ := by ring
    _ = _ := by rw [hn, one_mul]

/-- The constructed positive exact-fiber channel supplies the rectangular
isometry required above; support and normalization are the one-block inputs. -/
theorem norm_channel_phaseExpectation_le (g : Y → Bool) (u : Bool → Y → ℂ)
    (hsupport : ∀ b y, u b y ≠ 0 → g y = b)
    (hnorm : ∀ b, ∑ y, ‖u b y‖ ^ 2 = 1)
    (R : Matrix (ι → Y) (ι → Y) ℂ) (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (t : ℂ) (ht : ‖t‖ = 1) :
    ‖TensorPhase.phaseExpectation z t (FiberChannel.productW u * R * FiberChannel.productV u)‖ ≤
      ‖HilbertPointBridge.matrixOperator R‖ := by
  exact norm_compressed_phaseExpectation_le (FiberChannel.productV u)
    (FiberChannel.productW_mul_productV g u hsupport hnorm) R z hz t ht

theorem standard_phase_norm {k : ℕ} (hk : 0 < k) (j : ℕ) :
    ‖Complex.I * PhaseAverage.standardRoot k ^ j‖ = 1 := by
  have hroot : ‖PhaseAverage.standardRoot k‖ = 1 :=
    (PhaseAverage.standardRoot_primitive hk).norm'_eq_one (by omega)
  simp [norm_pow, hroot]

/-- For the fully constructed inner channel, a norm bound on the actual raw
commutator supplies every required phase sample. The operator bound is the
remaining analytic input; no compression or phase-norm premise is retained. -/
theorem fourier_level_bound_of_raw_commutator {σ : Type*}
    {coords : Y → σ → ℝ} {g : Y → Bool} {d : ℕ} {ε : ℝ}
    (w : ConstructedExtraction.InnerData coords g d ε)
    (p : (ι → Y) → ℂ) {k D : ℕ} (hk : 0 < k) {M : ℝ}
    (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (hbound : ‖HilbertPointBridge.matrixOperator
      (OperatorExtraction.rawCommutator
        (fun i => OperatorGrading.localLift (DegreeScaleWitness.witnessMatrix w.psi coords d) i)
        p k)‖ ≤ (D : ℝ) ^ k * M) :
    ‖TensorPhase.fourierLevel k
      (WalshReconstruction.coefficient (FiberChannel.channelQ w.u p)) z‖ ≤
      M / (2 * (k.factorial : ℝ)) *
        ((D : ℝ) / ‖DegreeScaleWitness.witnessStrip w.psi coords g d‖) ^ k := by
  apply w.fourier_level_bound p hk z hz
  intro j hj
  exact (norm_channel_phaseExpectation_le g w.u w.support w.normalized _ z hz
    (Complex.I * PhaseAverage.standardRoot k ^ j) (standard_phase_norm hk j)).trans hbound

end

end ApproxDegree.PhaseHilbertBridge
end

-- RawPolynomialBound.lean
section
/-!
# The actual raw-polynomial commutator and Fourier bounds

The matrix iteration used by extraction is transported to continuous Hilbert
operators by an algebra equivalence. Its generator, projection resolution,
and bandwidth are the actual tensor filtration objects. The only polynomial
hypotheses are total degree and a pointwise bound on its evaluations.
-/

open scoped BigOperators

namespace ApproxDegree.RawPolynomialBound

open HilbertPointBridge TensorFiltrationBandwidth

noncomputable section

variable {X ι Y σ : Type*} [Fintype X] [DecidableEq X]
  [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]

/-- The concrete matrix action preserves the full algebra structure. -/
def matrixOperatorEquiv : Matrix X X ℂ ≃ₐ[ℂ] (PointHilbert X →L[ℂ] PointHilbert X) :=
  (Matrix.toLpLinAlgEquiv 2).trans (Module.End.toContinuousLinearMap (PointHilbert X))

theorem matrixOperatorEquiv_apply (K : Matrix X X ℂ) :
    matrixOperatorEquiv K = matrixOperator K := rfl

theorem matrixOperator_mul (K L : Matrix X X ℂ) :
    matrixOperator (K * L) = matrixOperator K * matrixOperator L :=
  map_mul matrixOperatorEquiv K L

theorem matrixOperator_sub (K L : Matrix X X ℂ) :
    matrixOperator (K - L) = matrixOperator K - matrixOperator L :=
  map_sub matrixOperatorEquiv K L

theorem matrixOperator_smul (c : ℂ) (K : Matrix X X ℂ) :
    matrixOperator (c • K) = c • matrixOperator K :=
  map_smul matrixOperatorEquiv c K

theorem matrixOperator_sum {A : Type*} (s : Finset A) (K : A → Matrix X X ℂ) :
    matrixOperator (∑ a ∈ s, K a) = ∑ a ∈ s, matrixOperator (K a) :=
  map_sum matrixOperatorEquiv K s

theorem matrixOperator_zero : matrixOperator (0 : Matrix X X ℂ) = 0 :=
  map_zero matrixOperatorEquiv

theorem matrixOperator_one : matrixOperator (1 : Matrix X X ℂ) = 1 :=
  map_one matrixOperatorEquiv

omit [DecidableEq ι] in
/-- Transport of the exact raw matrix commutator, including every iterate. -/
theorem matrixOperator_rawCommutator (H : ι → Matrix X X ℂ) (p : X → ℂ) (k : ℕ) :
    matrixOperator (OperatorExtraction.rawCommutator H p k) =
      (fun T => matrixOperator (∑ i, H i) * T - T * matrixOperator (∑ i, H i))^[k]
        (matrixOperator (Matrix.diagonal p)) := by
  unfold OperatorExtraction.rawCommutator
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [matrixCommutator] at ih
    simp only [Function.iterate_succ_apply', matrixCommutator,
      matrixOperator_sub, matrixOperator_mul, ih]

/-- The actual product spectral projections acting on the Hilbert space. -/
def productLevelOperator (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (a : ι → Fin (d + 1)) : PointHilbert (ι → Y) →L[ℂ] PointHilbert (ι → Y) :=
  matrixOperator (productProjection (localLevelMatrix d ψ coords) a)

theorem productLevelOperator_resolution (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ) :
    ProjectionCommutator.IsResolution (productLevelOperator (ι := ι) d ψ coords) := by
  obtain ⟨hself, hidem, horth, htotal⟩ := actual_product_resolution (ι := ι) d ψ coords
  refine ⟨fun a => matrixOperator_isSelfAdjoint _ (hself a), ?_, ?_, ?_⟩
  · intro a
    change matrixOperator _ * matrixOperator _ = matrixOperator _
    rw [← matrixOperator_mul, hidem]
  · intro a b hab
    change matrixOperator _ * matrixOperator _ = 0
    rw [← matrixOperator_mul, horth a b hab, matrixOperator_zero]
  · change (∑ a, matrixOperator _) = 1
    rw [← matrixOperator_sum, htotal, matrixOperator_one]

theorem actual_generator_eq_spectral_sum (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ) :
    matrixOperator (∑ i : ι,
      OperatorGrading.localLift (DegreeScaleWitness.witnessMatrix ψ coords d) i) =
      ∑ a : ι → Fin (d + 1), (energy a : ℂ) • productLevelOperator d ψ coords a := by
  rw [product_generator_spectral_expansion, matrixOperator_sum]
  simp only [matrixOperator_smul, productLevelOperator]

/-- Coordinates of all raw blocks, indexed by the block/coordinate pair. -/
def productCoords (coords : Y → σ → ℝ) (x : ι → Y) (v : ι × σ) : ℝ :=
  coords (x v.1) v.2

/-- The actual raw real polynomial evaluated and included in the complex scalars. -/
def rawEval (coords : Y → σ → ℝ) (p : MvPolynomial (ι × σ) ℝ) (x : ι → Y) : ℂ :=
  (MvPolynomial.eval (productCoords coords x) p : ℂ)

variable [Fintype σ]

theorem actual_polynomial_bandwidth (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (p : MvPolynomial (ι × σ) ℝ) (D : ℕ) (hp : p.totalDegree ≤ D) :
    ProjectionCommutator.HasBandwidth (productLevelOperator (ι := ι) d ψ coords)
      energy D (matrixOperator (Matrix.diagonal (rawEval coords p))) := by
  intro a b hab
  change matrixOperator _ * matrixOperator _ * matrixOperator _ = 0
  rw [← matrixOperator_mul, ← matrixOperator_mul]
  have h := rawPolynomial_product_bandwidth d ψ coords p D hp a b hab
  change matrixOperator (productProjection (localLevelMatrix d ψ coords) a *
    polynomialMatrix (productCoords coords) p *
    productProjection (localLevelMatrix d ψ coords) b) = 0
  unfold productCoords
  rw [h, matrixOperator_zero]

omit [Fintype σ] in
/-- The pointwise polynomial bound is the genuine diagonal operator bound. -/
theorem norm_polynomial_operator_le (coords : Y → σ → ℝ)
    (p : MvPolynomial (ι × σ) ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ x : ι → Y, |MvPolynomial.eval (productCoords coords x) p| ≤ M) :
    ‖matrixOperator (Matrix.diagonal (rawEval coords p))‖ ≤ M := by
  apply WeightedPolynomialAction.pointMultiplier_opNorm_le _ M hM
  intro x
  simpa only [rawEval, Complex.norm_real, Real.norm_eq_abs] using hp x

/-- The raw commutator bound needed by the extraction theorem, derived from
the actual polynomial's degree and pointwise bound. -/
theorem norm_rawCommutator_le (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (p : MvPolynomial (ι × σ) ℝ) (D : ℕ) (hdeg : p.totalDegree ≤ D)
    (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ x : ι → Y, |MvPolynomial.eval (productCoords coords x) p| ≤ M) (k : ℕ) :
    ‖matrixOperator (OperatorExtraction.rawCommutator
      (fun i => OperatorGrading.localLift (DegreeScaleWitness.witnessMatrix ψ coords d) i)
      (rawEval coords p) k)‖ ≤ ((7 * D : ℕ) : ℝ) ^ k * M := by
  rw [matrixOperator_rawCommutator]
  calc
    _ ≤ ((7 * D : ℕ) : ℝ) ^ k *
        ‖matrixOperator (Matrix.diagonal (rawEval coords p))‖ :=
      ProjectionCommutator.norm_iterated_commutator_le_of_generator_eq
        (productLevelOperator d ψ coords) (productLevelOperator_resolution d ψ coords)
        energy _ (actual_generator_eq_spectral_sum d ψ coords) D _
        (actual_polynomial_bandwidth d ψ coords p D hdeg) k
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_polynomial_operator_le coords p M hM hp)
      (by positivity)

/-- Constructed uniform Fourier-level extraction from an actual bounded raw
polynomial. No raw-commutator or phase-sample estimate is an input. -/
theorem fourier_level_bound {coords : Y → σ → ℝ} {g : Y → Bool} {d : ℕ} {ε : ℝ}
    (w : ConstructedExtraction.InnerData coords g d ε)
    (p : MvPolynomial (ι × σ) ℝ) (D : ℕ) (hdeg : p.totalDegree ≤ D)
    (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ x : ι → Y, |MvPolynomial.eval (productCoords coords x) p| ≤ M)
    {k : ℕ} (hk : 0 < k) (z : ι → ℂ) (hz : ∀ i, z i * z i = 1) :
    ‖TensorPhase.fourierLevel k
      (WalshReconstruction.coefficient (FiberChannel.channelQ w.u (rawEval coords p))) z‖ ≤
      M / (2 * (k.factorial : ℝ)) *
        (((7 * D : ℕ) : ℝ) / ‖DegreeScaleWitness.witnessStrip w.psi coords g d‖) ^ k := by
  exact PhaseHilbertBridge.fourier_level_bound_of_raw_commutator w (rawEval coords p)
    hk z hz (norm_rawCommutator_le d w.psi coords p D hdeg M hM hp k)

end

end ApproxDegree.RawPolynomialBound
end

-- BlockDiagonal.lean
section
/-! A single matched block diagonal is contractive for the genuine Hilbert
operator norm. No phase averaging or entrywise matrix norm is used. -/

namespace ElementaryComposition.BlockDiagonal
open scoped BigOperators
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype ι]

structure OrthogonalProjections (P : ι → E →L[ℂ] E) : Prop where
  selfAdjoint : ∀ i, IsSelfAdjoint (P i)
  idempotent : ∀ i, P i * P i = P i
  orthogonal : ∀ i j, i ≠ j → P i * P j = 0

lemma projection_norm_le (P : E →L[ℂ] E) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) (x : E) : ‖P x‖ ≤ ‖x‖ := by
  have hinner : inner ℂ (P x) (P x) = inner ℂ x (P x) := by
    calc
      _ = inner ℂ x (P (P x)) := hP.isSymmetric x (P x)
      _ = _ := by
        have h := congrArg (fun A : E →L[ℂ] E => A x) hPP
        simpa only [mul_apply_eq_comp] using congrArg (inner ℂ x) h
  have hbound : ‖P x‖ ^ 2 ≤ ‖x‖ * ‖P x‖ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  nlinarith [norm_nonneg x, norm_nonneg (P x)]

omit [Fintype ι] in
lemma OrthogonalProjections.inner_apply (P : ι → E →L[ℂ] E)
    (hP : OrthogonalProjections P) (i j : ι) (x y : E) (hij : i ≠ j) :
    inner ℂ (P i x) (P j y) = 0 := by
  calc
    _ = inner ℂ x (P i (P j y)) := (hP.selfAdjoint i).isSymmetric x (P j y)
    _ = 0 := by
      have h := congrArg (fun A : E →L[ℂ] E => A y) (hP.orthogonal i j hij)
      simp only [mul_apply_eq_comp, zero_apply] at h
      rw [h, inner_zero_right]

lemma OrthogonalProjections.norm_sum_sq (P : ι → E →L[ℂ] E)
    (hP : OrthogonalProjections P) (x : ι → E) :
    ‖∑ i, P i (x i)‖ ^ 2 = ∑ i, ‖P i (x i)‖ ^ 2 := by
  classical
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner, inner_sum]
  change (RCLike.reCLM : ℂ →L[ℝ] ℝ) _ = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rfl
  · intro j _ hji
    rw [hP.inner_apply P j i _ _ hji]
    rfl
  · simp

lemma OrthogonalProjections.sum_sq_le (P : ι → E →L[ℂ] E)
    (hP : OrthogonalProjections P) (x : E) :
    ∑ i, ‖P i x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have hin : RCLike.re (inner ℂ x (∑ i, P i x)) = ∑ i, ‖P i x‖ ^ 2 := by
    simp only [inner_sum]
    change (RCLike.reCLM : ℂ →L[ℝ] ℝ) _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hs : inner ℂ (P i x) (P i x) = inner ℂ x (P i (P i x)) :=
      (hP.selfAdjoint i).isSymmetric x (P i x)
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hs]
    have hi := congrArg (fun A : E →L[ℂ] E => A x) (hP.idempotent i)
    simp only [mul_apply_eq_comp] at hi
    rw [hi]
    rfl
  have hnorm := hP.norm_sum_sq P (fun _ => x)
  have h := norm_sub_sq (𝕜 := ℂ) x (∑ i, P i x)
  rw [hin, hnorm] at h
  nlinarith [sq_nonneg ‖x - ∑ i, P i x‖]

/-- Keeping blocks with mutually orthogonal source and target spaces never
increases the genuine Hilbert operator norm. Completeness of either family
is unnecessary, so this includes partial block diagonals. -/
theorem norm_sum_blocks_le (P Q : ι → E →L[ℂ] E)
    (hP : OrthogonalProjections P) (hQ : OrthogonalProjections Q)
    (T : E →L[ℂ] E) : ‖∑ i, P i * T * Q i‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) 
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simp only [sum_apply, mul_apply_eq_comp]
  rw [hP.norm_sum_sq P]
  calc
    (∑ i, ‖P i (T (Q i x))‖ ^ 2) ≤ ∑ i, (‖T‖ * ‖Q i x‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      exact (projection_norm_le (P i) (hP.selfAdjoint i) (hP.idempotent i) _).trans
        (T.le_opNorm _)
    _ = ‖T‖ ^ 2 * ∑ i, ‖Q i x‖ ^ 2 := by simp_rw [mul_pow]; rw [Finset.mul_sum]
    _ ≤ ‖T‖ ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left (hQ.sum_sq_le Q x) (sq_nonneg _)
    _ = (‖T‖ * ‖x‖) ^ 2 := (mul_pow _ _ _).symm

section Coordinate
open ApproxDegree.SpectralCommutator
variable {X : Type*} [Fintype X] [DecidableEq X]

def gradeProjection (q : X → ℤ) (r : ℤ) : Hilbert X →L[ℂ] Hilbert X :=
  matrixOp (Matrix.diagonal (fun a => if q a = r then 1 else 0))

@[simp] theorem gradeProjection_apply (q : X → ℤ) (r : ℤ) (v : Hilbert X) (a : X) :
    gradeProjection q r v a = if q a = r then v a else 0 := by
  change (Matrix.diagonal (fun a => if q a = r then (1 : ℂ) else 0)).mulVec v a = _
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

lemma gradeProjection_selfAdjoint (q : X → ℤ) (r : ℤ) :
    IsSelfAdjoint (gradeProjection q r) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro v w
  change inner ℂ (gradeProjection q r v) w = inner ℂ v (gradeProjection q r w)
  simp only [PiLp.inner_apply, RCLike.inner_apply', gradeProjection_apply]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma gradeProjection_mul_self (q : X → ℤ) (r : ℤ) :
    gradeProjection q r * gradeProjection q r = gradeProjection q r := by
  ext v a
  simp only [mul_apply_eq_comp, gradeProjection_apply]
  split_ifs <;> rfl

lemma gradeProjection_mul_eq_zero (q : X → ℤ) (r s : ℤ) (h : r ≠ s) :
    gradeProjection q r * gradeProjection q s = 0 := by
  ext v a
  simp only [mul_apply_eq_comp, gradeProjection_apply, zero_apply]
  split_ifs <;> simp_all

def shiftMask (q : X → ℤ) (s : ℤ) (A : Matrix X X ℂ) : Matrix X X ℂ :=
  fun a b => if q a - q b = s then A a b else 0

/-- Selecting one grade difference contracts the actual Euclidean operator norm.
The grade fibers may have arbitrary dimensions. -/
theorem norm_shiftMask_le (q : X → ℤ) (s : ℤ) (A : Matrix X X ℂ) :
    ‖matrixOp (shiftMask q s A)‖ ≤ ‖matrixOp A‖ := by
  classical
  let grades := Finset.univ.image q
  let P : grades → Hilbert X →L[ℂ] Hilbert X := fun r => gradeProjection q (r.val + s)
  let Q : grades → Hilbert X →L[ℂ] Hilbert X := fun r => gradeProjection q r.val
  have hP : OrthogonalProjections P := by
    refine ⟨fun r => gradeProjection_selfAdjoint q _, fun r => gradeProjection_mul_self q _, ?_⟩
    intro r t hrt
    apply gradeProjection_mul_eq_zero
    intro h
    apply hrt
    apply Subtype.ext
    omega
  have hQ : OrthogonalProjections Q := by
    refine ⟨fun r => gradeProjection_selfAdjoint q _, fun r => gradeProjection_mul_self q _, ?_⟩
    intro r t hrt
    apply gradeProjection_mul_eq_zero
    exact fun h => hrt (Subtype.ext h)
  have heq : (∑ r, P r * matrixOp A * Q r) = matrixOp (shiftMask q s A) := by
    ext v a
    simp only [sum_apply, mul_apply_eq_comp]
    change (∑ r : grades, gradeProjection q (r.val + s)
      (matrixOp A (gradeProjection q r.val v))) a = _
    simp only [WithLp.ofLp_sum, Finset.sum_apply, gradeProjection_apply, matrixOp_apply, shiftMask]
    have hterm (r : grades) :
        (if q a = r.val + s then ∑ b, A a b * (if q b = r.val then v b else 0) else 0) =
        ∑ b, if q b = r.val then (if q a - q b = s then A a b * v b else 0) else 0 := by
      by_cases ha : q a = r.val + s
      · simp only [ha, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : q b = r.val
        · simp only [hb, ↓reduceIte]
          simp
        · simp [hb]
      · simp only [ha, ↓reduceIte]
        symm
        apply Finset.sum_eq_zero
        intro b _
        by_cases hb : q b = r.val
        · simp only [hb, ↓reduceIte]
          rw [if_neg (show q a - r.val ≠ s by omega)]
        · simp [hb]
    simp_rw [hterm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    let rb : grades := ⟨q b, Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩⟩
    rw [Finset.sum_eq_single rb]
    · simp only [rb, ↓reduceIte]
      split_ifs <;> simp
    · intro r _ hr
      have hbr : q b ≠ r.val := by
        intro h
        apply hr
        exact Subtype.ext h.symm
      simp [hbr]
    · simp
  rw [← heq]
  exact norm_sum_blocks_le P Q hP hQ _

end Coordinate
end
end ElementaryComposition.BlockDiagonal
end

-- ElementaryBandwidth.lean
section
/-!
# Elementary bandwidth bound by interval binning

This file uses the genuine Euclidean operator norm. The eigenvalues used by
our polynomial filtration are integers, so integer division gives the spectral
bins exactly. No scalar Bernstein theorem is used in the proofs below.
-/

namespace ElementaryComposition.ElementaryBandwidth

set_option linter.unusedSectionVars false

open ApproxDegree.SpectralCommutator
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Select one signed block diagonal of an integer labeling. -/
def shiftPart (q : X → ℤ) (s : ℤ) (A : Matrix X X ℂ) : Matrix X X ℂ :=
  fun a b => if q a - q b = s then A a b else 0

/-- Eigenvalues distance at most D lie in equal or neighboring D-wide bins. -/
theorem bin_difference_le_one (a b D : ℤ) (hD : 0 < D)
    (h : |a - b| ≤ D) : |a / D - b / D| ≤ 1 := by
  have ha := Int.emod_add_mul_ediv a D
  have hb := Int.emod_add_mul_ediv b D
  have ha0 := Int.emod_nonneg a (ne_of_gt hD)
  have hb0 := Int.emod_nonneg b (ne_of_gt hD)
  have ha1 := Int.emod_lt_of_pos a hD
  have hb1 := Int.emod_lt_of_pos b hD
  rcases abs_le.mp h with ⟨hl, hu⟩
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The centered within-bin eigenvalue. -/
def centeredRemainder (e : X → ℤ) (D : ℕ) (a : X) : ℂ :=
  ((e a % (D : ℤ) : ℤ) : ℂ) - (D : ℂ) / 2

theorem norm_centeredRemainder_le (e : X → ℤ) (D : ℕ) (hD : 0 < D) (a : X) :
    ‖centeredRemainder e D a‖ ≤ (D : ℝ) / 2 := by
  have hD' : (0 : ℤ) < D := by exact_mod_cast hD
  have hlow : (0 : ℝ) ≤ (e a % (D : ℤ) : ℤ) := by
    exact_mod_cast Int.emod_nonneg (e a) (ne_of_gt hD')
  have hupp : ((e a % (D : ℤ) : ℤ) : ℝ) < D := by
    exact_mod_cast Int.emod_lt_of_pos (e a) hD'
  have heq : centeredRemainder e D a =
      (((e a % (D : ℤ) : ℤ) : ℝ) - (D : ℝ) / 2 : ℝ) := by
    simp [centeredRemainder]
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith

theorem norm_centered_diagonal_le (e : X → ℤ) (D : ℕ) (hD : 0 < D) :
    ‖Matrix.diagonal (centeredRemainder e D)‖ ≤ (D : ℝ) / 2 := by
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  exact norm_centeredRemainder_le e D hD

/-- Separating the bin number from its centered remainder. -/
theorem eigenvalue_decomposition (e : X → ℤ) (D : ℕ) (a : X) :
    (e a : ℂ) = (D : ℂ) * ((e a / (D : ℤ) : ℤ) : ℂ) +
      centeredRemainder e D a + (D : ℂ) / 2 := by
  have h := Int.emod_add_mul_ediv (e a) (D : ℤ)
  have hc : (((e a % (D : ℤ)) : ℤ) : ℂ) +
      (D : ℂ) * (((e a / (D : ℤ)) : ℤ) : ℂ) = (e a : ℂ) := by
    exact_mod_cast h
  unfold centeredRemainder
  linear_combination -hc

/-- The bin-number commutator has only its two neighboring block diagonals. -/
theorem bin_commutator_eq (e : X → ℤ) (D : ℕ) (hD : 0 < D)
    (A : Matrix X X ℂ) (hband : HasBandwidth e D A) :
    diagonalCommutator (fun a => e a / (D : ℤ)) A =
      shiftPart (fun a => e a / (D : ℤ)) 1 A -
      shiftPart (fun a => e a / (D : ℤ)) (-1) A := by
  ext a b
  rw [diagonalCommutator_apply]
  by_cases h : |e a - e b| ≤ (D : ℤ)
  · have hsmall := bin_difference_le_one (e a) (e b) D (by exact_mod_cast hD) h
    have hcases : e a / (D : ℤ) - e b / (D : ℤ) = -1 ∨
        e a / (D : ℤ) - e b / (D : ℤ) = 0 ∨
        e a / (D : ℤ) - e b / (D : ℤ) = 1 := by
      have := abs_le.mp hsmall
      omega
    rcases hcases with he | he | he <;> simp [shiftPart, he]
  · have hz := hband a b (lt_of_not_ge h)
    simp [shiftPart, hz]

/-- Exact decomposition used for the elementary factor-three estimate. -/
theorem commutator_decomposition (e : X → ℤ) (D : ℕ) (A : Matrix X X ℂ) :
    diagonalCommutator e A =
      (D : ℂ) • diagonalCommutator (fun a => e a / (D : ℤ)) A +
      (Matrix.diagonal (centeredRemainder e D) * A -
        A * Matrix.diagonal (centeredRemainder e D)) := by
  ext a b
  simp only [diagonalCommutator_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [Int.cast_sub, Int.cast_sub]
  rw [eigenvalue_decomposition e D a, eigenvalue_decomposition e D b]
  ring

/-- Once the two neighboring block diagonals are contractions, interval binning
proves the genuine Hilbert operator norm estimate, with no analytic inequality. -/
theorem norm_commutator_le_three_of_shift_bounds
    (e : X → ℤ) (D : ℕ) (hD : 0 < D) (A : Matrix X X ℂ)
    (hband : HasBandwidth e D A)
    (hplus : ‖shiftPart (fun a => e a / (D : ℤ)) 1 A‖ ≤ ‖A‖)
    (hminus : ‖shiftPart (fun a => e a / (D : ℤ)) (-1) A‖ ≤ ‖A‖) :
    ‖diagonalCommutator e A‖ ≤ (3 * D : ℝ) * ‖A‖ := by
  have hbin : ‖diagonalCommutator (fun a => e a / (D : ℤ)) A‖ ≤ 2 * ‖A‖ := by
    rw [bin_commutator_eq e D hD A hband]
    exact (norm_sub_le _ _).trans (by linarith)
  have hrem : ‖Matrix.diagonal (centeredRemainder e D) * A -
      A * Matrix.diagonal (centeredRemainder e D)‖ ≤ (D : ℝ) * ‖A‖ := by
    calc
      _ ≤ ‖Matrix.diagonal (centeredRemainder e D) * A‖ +
          ‖A * Matrix.diagonal (centeredRemainder e D)‖ := norm_sub_le _ _
      _ ≤ ‖Matrix.diagonal (centeredRemainder e D)‖ * ‖A‖ +
          ‖A‖ * ‖Matrix.diagonal (centeredRemainder e D)‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ((D : ℝ) / 2) * ‖A‖ + ‖A‖ * ((D : ℝ) / 2) := by
        gcongr <;> exact norm_centered_diagonal_le e D hD
      _ = _ := by ring
  rw [commutator_decomposition]
  calc
    _ ≤ ‖(D : ℂ) • diagonalCommutator (fun a => e a / (D : ℤ)) A‖ +
        ‖Matrix.diagonal (centeredRemainder e D) * A -
          A * Matrix.diagonal (centeredRemainder e D)‖ := norm_add_le _ _
    _ = (D : ℝ) * ‖diagonalCommutator (fun a => e a / (D : ℤ)) A‖ +
        ‖Matrix.diagonal (centeredRemainder e D) * A -
          A * Matrix.diagonal (centeredRemainder e D)‖ := by rw [norm_smul]; simp
    _ ≤ (D : ℝ) * (2 * ‖A‖) + (D : ℝ) * ‖A‖ := by gcongr
    _ = _ := by ring

/-- Bandwidth zero means the actual commutator vanishes. -/
theorem commutator_eq_zero_of_bandwidth_zero (e : X → ℤ)
    (A : Matrix X X ℂ) (hband : HasBandwidth e 0 A) :
    diagonalCommutator e A = 0 := by
  ext a b
  rw [diagonalCommutator_apply]
  by_cases he : e a = e b
  · simp [he]
  · have hz := hband a b (by simpa using abs_pos.mpr (sub_ne_zero.mpr he))
    simp [hz]

/-- Elementary bandwidth theorem, including the constant case. The two
block-contraction hypotheses of the local estimate are discharged. -/
theorem norm_commutator_le_three (e : X → ℤ) (D : ℕ)
    (A : Matrix X X ℂ) (hband : HasBandwidth e D A) :
    ‖diagonalCommutator e A‖ ≤ (3 * D : ℝ) * ‖A‖ := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · rw [commutator_eq_zero_of_bandwidth_zero e A hband]
    simp
  · apply norm_commutator_le_three_of_shift_bounds e D hD A hband
    · change ‖matrixOp (shiftPart (fun a => e a / (D : ℤ)) 1 A)‖ ≤ ‖matrixOp A‖
      exact
        BlockDiagonal.norm_shiftMask_le (fun a => e a / (D : ℤ)) 1 A
    · change ‖matrixOp (shiftPart (fun a => e a / (D : ℤ)) (-1) A)‖ ≤ ‖matrixOp A‖
      exact
        BlockDiagonal.norm_shiftMask_le (fun a => e a / (D : ℤ)) (-1) A

/-- Iterating the elementary bound is valid because the commutator preserves
all the original zero entries. -/
theorem norm_iterate_commutator_le_three (e : X → ℤ) (D : ℕ)
    (A : Matrix X X ℂ) (hband : HasBandwidth e D A) (k : ℕ) :
    ‖((diagonalCommutator e)^[k] A)‖ ≤ (3 * D : ℝ) ^ k * ‖A‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ (3 * D : ℝ) * ‖((diagonalCommutator e)^[k] A)‖ :=
        norm_commutator_le_three e D _
          (hasBandwidth_iterate_diagonalCommutator e D A hband k)
      _ ≤ (3 * D : ℝ) * ((3 * D : ℝ) ^ k * ‖A‖) := by gcongr
      _ = _ := by ring

/-- The elementary theorem stated directly for genuine Hilbert operators. -/
theorem norm_iterated_hilbertCommutator_le_three (e : X → ℤ) (D : ℕ)
    (A : Matrix X X ℂ) (hband : HasBandwidth e D A) (k : ℕ) :
    ‖(fun T => weightOperator e * T - T * weightOperator e)^[k] (matrixOp A)‖ ≤
      (3 * D : ℝ) ^ k * ‖matrixOp A‖ := by
  rw [← matrixOp_iterate_diagonalCommutator]
  exact norm_iterate_commutator_le_three e D A hband k


end
end ElementaryComposition.ElementaryBandwidth
end

-- ProjectionBandwidth.lean
section
namespace ElementaryComposition.ProjectionBandwidth
open scoped BigOperators
open ApproxDegree.ProjectionCommutator
open BlockDiagonal
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype ι]

lemma resolution_orthogonal (R : ι → E →L[ℂ] E) (hR : IsResolution R) :
    OrthogonalProjections R := ⟨hR.selfAdjoint, hR.idempotent, hR.orthogonal⟩

def grouped (R : ι → E →L[ℂ] E) (q : ι → ℤ) (r : ℤ) : E →L[ℂ] E :=
  spectralSum R (fun a => if q a = r then 1 else 0)

lemma grouped_selfAdjoint (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (q : ι → ℤ) (r : ℤ) : IsSelfAdjoint (grouped R q r) := by
  change star (spectralSum R _) = spectralSum R _
  rw [spectralSum_star R hR]
  congr 1
  funext a
  split_ifs <;> simp

lemma grouped_mul_self (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (q : ι → ℤ) (r : ℤ) : grouped R q r * grouped R q r = grouped R q r := by
  unfold grouped
  rw [spectralSum_mul R hR]
  congr 1
  funext a
  split_ifs <;> simp

lemma grouped_mul_zero (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (q : ι → ℤ) (r s : ℤ) (hrs : r ≠ s) : grouped R q r * grouped R q s = 0 := by
  unfold grouped
  rw [spectralSum_mul R hR]
  have hcoef : (fun a => (if q a = r then (1:ℂ) else 0) *
      (if q a = s then 1 else 0)) = fun _ => 0 := by
    funext a
    split_ifs <;> simp_all
  rw [hcoef]
  simp [spectralSum]

lemma eq_of_blocks_eq (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (A B : E →L[ℂ] E) (h : ∀ a b, R a * A * R b = R a * B * R b) : A = B := by
  rw [← sum_blocks R hR A, ← sum_blocks R hR B]
  exact Finset.sum_congr rfl fun r _ => h r.1 r.2

/-- Select a single signed diagonal after grouping the original resolution. -/
def select (R : ι → E →L[ℂ] E) (q : ι → ℤ) (s : ℤ) (B : E →L[ℂ] E) : E →L[ℂ] E :=
  ∑ r : (Finset.univ.image q), grouped R q (r.val + s) * B * grouped R q r.val

lemma norm_select_le (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (q : ι → ℤ) (s : ℤ) (B : E →L[ℂ] E) : ‖select R q s B‖ ≤ ‖B‖ := by
  classical
  apply norm_sum_blocks_le
  · refine ⟨fun _ => grouped_selfAdjoint R hR q _, fun _ => grouped_mul_self R hR q _, ?_⟩
    intro a b hab
    apply grouped_mul_zero R hR
    intro h
    apply hab
    apply Subtype.ext
    omega
  · refine ⟨fun _ => grouped_selfAdjoint R hR q _, fun _ => grouped_mul_self R hR q _, ?_⟩
    intro a b hab
    apply grouped_mul_zero R hR
    exact fun h => hab (Subtype.ext h)

lemma select_block (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (q : ι → ℤ) (s : ℤ) (B : E →L[ℂ] E) (a b : ι) :
    R a * select R q s B * R b =
      if q a - q b = s then R a * B * R b else 0 := by
  classical
  unfold select
  rw [Finset.mul_sum, Finset.sum_mul]
  have hterm (r : (Finset.univ.image q)) :
      R a * (grouped R q (r.val+s) * B * grouped R q r.val) * R b =
      if q b = r.val then (if q a - q b = s then R a * B * R b else 0) else 0 := by
    calc
      _ = (R a * grouped R q (r.val+s)) * B * (grouped R q r.val * R b) := by noncomm_ring
      _ = _ := by
        unfold grouped
        rw [projection_mul_spectralSum R hR, spectralSum_mul_projection R hR]
        by_cases hb : q b = r.val
        · simp only [hb, ↓reduceIte, one_smul]
          by_cases ha : q a = r.val+s
          · simp [ha]
          · have hh : q a-r.val≠s := by omega
            simp [ha, hh]
        · simp [hb]
  simp_rw [hterm]
  let rb : (Finset.univ.image q) := ⟨q b, Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩⟩
  rw [Finset.sum_eq_single rb]
  · simp [rb]
  · intro r _ hr
    have hbr : q b ≠ r.val := fun h => hr (Subtype.ext h.symm)
    simp [hbr]
  · simp

lemma norm_spectralSum_le (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (c : ι → ℂ) (t : ℝ) (ht : 0 ≤ t) (hc : ∀ a, ‖c a‖ ≤ t) :
    ‖spectralSum R c‖ ≤ t := by
  apply ContinuousLinearMap.opNorm_le_bound _ ht
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht (norm_nonneg _))).mp
  have heq : spectralSum R c x = ∑ a, R a (c a • x) := by
    simp [spectralSum, sum_apply, smul_apply, map_smul]
  rw [heq, (resolution_orthogonal R hR).norm_sum_sq R]
  calc
    _ ≤ ∑ a, t^2 * ‖R a x‖^2 := by
      apply Finset.sum_le_sum
      intro a _
      rw [map_smul, norm_smul, mul_pow]
      exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) ht).mpr (hc a)) (sq_nonneg _)
    _ = t^2 * ∑ a, ‖R a x‖^2 := (Finset.mul_sum ..).symm
    _ ≤ t^2 * ‖x‖^2 := mul_le_mul_of_nonneg_left
      ((resolution_orthogonal R hR).sum_sq_le R x) (sq_nonneg _)
    _ = (t * ‖x‖)^2 := (mul_pow _ _ _).symm

lemma bin_commutator_eq (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (D : ℕ) (hD : 0 < D) (B : E →L[ℂ] E)
    (hband : HasBandwidth R e D B) :
    commutator R (fun a => e a / (D : ℤ)) B =
      select R (fun a => e a / (D : ℤ)) 1 B - select R (fun a => e a / (D : ℤ)) (-1) B := by
  apply eq_of_blocks_eq R hR
  intro a b
  rw [block_commutator R hR, mul_sub, sub_mul, select_block R hR, select_block R hR]
  by_cases h : |e a-e b| ≤ (D : ℤ)
  · have hsmall := ElementaryBandwidth.bin_difference_le_one (e a) (e b) D
      (by exact_mod_cast hD) h
    have hcases : e a / (D:ℤ)-e b / (D:ℤ) = -1 ∨
        e a / (D:ℤ)-e b / (D:ℤ) = 0 ∨ e a / (D:ℤ)-e b / (D:ℤ) = 1 := by
      have := abs_le.mp hsmall
      omega
    rcases hcases with he | he | he <;> simp [he]
  · rw [hband a b (lt_of_not_ge h)]
    simp

lemma generator_decomposition (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (D : ℕ) :
    generator R e = (D : ℂ) • generator R (fun a => e a / (D : ℤ)) +
      spectralSum R (ElementaryBandwidth.centeredRemainder e D) + ((D : ℂ)/2) • 1 := by
  classical
  rw [← hR.total]
  simp only [generator, spectralSum, Finset.smul_sum, ← Finset.sum_add_distrib,
    smul_smul, ← add_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [ElementaryBandwidth.eigenvalue_decomposition e D a]

lemma commutator_decomposition (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (D : ℕ) (B : E →L[ℂ] E) :
    commutator R e B = (D : ℂ) • commutator R (fun a => e a / (D : ℤ)) B +
      (spectralSum R (ElementaryBandwidth.centeredRemainder e D) * B -
       B * spectralSum R (ElementaryBandwidth.centeredRemainder e D)) := by
  unfold ApproxDegree.ProjectionCommutator.commutator
  rw [generator_decomposition R hR e D]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_sub]
  abel

/-- Elementary constant-three bound on any complete complex Hilbert space
with a finite orthogonal integer spectral resolution. -/
theorem norm_commutator_le_three (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (D : ℕ) (B : E →L[ℂ] E) (hband : HasBandwidth R e D B) :
    ‖commutator R e B‖ ≤ (3 * D : ℝ) * ‖B‖ := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have hz : commutator R e B = 0 := by
      apply eq_of_blocks_eq R hR
      intro a b
      rw [block_commutator R hR]
      by_cases he : e a = e b
      · simp [he]
      · rw [hband a b (by simpa using abs_pos.mpr (sub_ne_zero.mpr he))]
        simp
    rw [hz]
    simp
  · have hbin : ‖commutator R (fun a => e a / (D : ℤ)) B‖ ≤ 2 * ‖B‖ := by
      rw [bin_commutator_eq R hR e D hD B hband]
      exact (norm_sub_le _ _).trans (by
        have h1 := norm_select_le R hR (fun a => e a / (D : ℤ)) 1 B
        have h2 := norm_select_le R hR (fun a => e a / (D : ℤ)) (-1) B
        linarith)
    have hcenter : ‖spectralSum R (ElementaryBandwidth.centeredRemainder e D)‖ ≤ (D : ℝ)/2 :=
      norm_spectralSum_le R hR _ _ (by positivity)
        (ElementaryBandwidth.norm_centeredRemainder_le e D hD)
    have hrem : ‖spectralSum R (ElementaryBandwidth.centeredRemainder e D) * B -
        B * spectralSum R (ElementaryBandwidth.centeredRemainder e D)‖ ≤ (D : ℝ) * ‖B‖ := by
      calc
        _ ≤ ‖spectralSum R (ElementaryBandwidth.centeredRemainder e D) * B‖ +
            ‖B * spectralSum R (ElementaryBandwidth.centeredRemainder e D)‖ := norm_sub_le _ _
        _ ≤ ‖spectralSum R (ElementaryBandwidth.centeredRemainder e D)‖ * ‖B‖ +
            ‖B‖ * ‖spectralSum R (ElementaryBandwidth.centeredRemainder e D)‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ ((D : ℝ)/2)*‖B‖ + ‖B‖*((D : ℝ)/2) := by gcongr
        _ = _ := by ring
    rw [commutator_decomposition R hR e D B]
    calc
      _ ≤ ‖(D : ℂ) • commutator R (fun a => e a / (D : ℤ)) B‖ +
          ‖spectralSum R (ElementaryBandwidth.centeredRemainder e D) * B -
           B * spectralSum R (ElementaryBandwidth.centeredRemainder e D)‖ := norm_add_le _ _
      _ = (D : ℝ) * ‖commutator R (fun a => e a / (D : ℤ)) B‖ +
          ‖spectralSum R (ElementaryBandwidth.centeredRemainder e D) * B -
           B * spectralSum R (ElementaryBandwidth.centeredRemainder e D)‖ := by rw [norm_smul]; simp
      _ ≤ (D : ℝ)*(2*‖B‖) + (D : ℝ)*‖B‖ := by gcongr
      _ = _ := by ring

/-- Iteration preserves the same spectral bandwidth. -/
theorem norm_iterated_commutator_le_three (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (D : ℕ) (B : E →L[ℂ] E) (hband : HasBandwidth R e D B) (k : ℕ) :
    ‖(commutator R e)^[k] B‖ ≤ (3 * D : ℝ)^k * ‖B‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ (3*D:ℝ)*‖(commutator R e)^[k] B‖ :=
        norm_commutator_le_three R hR e D _ (hasBandwidth_iterated_commutator R hR e D B hband k)
      _ ≤ (3*D:ℝ)*((3*D:ℝ)^k*‖B‖) := by gcongr
      _ = _ := by ring

theorem norm_iterated_commutator_le_of_generator_eq (R : ι → E →L[ℂ] E)
    (hR : IsResolution R) (e : ι → ℤ) (H : E →L[ℂ] E)
    (hH : H = ∑ a, (e a : ℂ) • R a) (D : ℕ) (B : E →L[ℂ] E)
    (hband : HasBandwidth R e D B) (k : ℕ) :
    ‖(fun T => H*T-T*H)^[k] B‖ ≤ (3*D:ℝ)^k*‖B‖ := by
  subst H
  exact norm_iterated_commutator_le_three R hR e D B hband k

end
end ElementaryComposition.ProjectionBandwidth
end


