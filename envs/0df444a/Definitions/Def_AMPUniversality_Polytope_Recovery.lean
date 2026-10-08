-- Prove2me | Definitions.Def_AMPUniversality_Polytope_Recovery
-- name    : AMPUniversality_Polytope_Recovery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:55.56293+00:00
-- url     : https://prove2.me/theorems/6f5549b1-d64a-4a91-8eae-208fa15680da
-- title:
--   Theorem 2 and equation (6.1) — random rectangular matrices and exact ℓ¹ recovery
-- statement:
--   For a matrix $A$ and signal $x_0$, exact basis-pursuit recovery means that $x_0$ is the unique minimum-one-norm solution among all $x$ with $Ax=Ax_0$:
--
--   $$Ax=Ax_0,\quad x\ne x_0\quad\Longrightarrow\quad\sum_i|x_{0,i}|<\sum_i|x_i|.$$
--
--   This module also defines the projected matrix $A=\widetilde A+\nu G$, the row count $m(n)=\lfloor n\delta\rfloor$, and predicates for independent sub-Gaussian matrix entries and an independent Gaussian component. The same predicates are used with the distinct variance normalizations of Theorems 2 and 8. Its signal predicate spells out Theorem 8's deterministic-signal and random-signal cases.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 5, Theorem 2; pp. 39–40, equation (6.1) and Theorem 8

import Mathlib

set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators NNReal Topology

namespace AMPUniversality.Polytope

/-- The unique solution of basis pursuit equals the specified signal. -/
def L1Succeeds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x0 : Fin n → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, Matrix.mulVec A x = Matrix.mulVec A x0 → x ≠ x0 →
    (∑ i, |x0 i|) < ∑ i, |x i|

/-- Scalar soft thresholding from (6.6). -/
noncomputable def softThreshold (u θ : ℝ) : ℝ :=
  Real.sign u * max (|u| - θ) 0

/-- The proportional row count used in Theorems 2 and 8. -/
noncomputable def rowCount (δ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) * δ⌋₊

/-- The Gaussian-perturbed matrix, kept as a function of its two components. -/
def perturbedMatrix {Ω : Type*} (m : ℕ → ℕ)
    (Atil G : ∀ n, Ω → Matrix (Fin (m n)) (Fin n) ℝ) (ν : ℝ) :
    ∀ n, Ω → Matrix (Fin (m n)) (Fin n) ℝ :=
  fun n ω => Atil n ω + ν • G n ω

/-- The entrywise assumptions common to the two rectangular random-matrix models. -/
def RectangularMatrixLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ → ℕ)
    (A : ∀ n, Ω → Matrix (Fin (m n)) (Fin n) ℝ)
    (variance : ℕ → ℝ) (scale : ℕ → ℝ≥0) : Prop :=
  ∀ n, Measurable (fun ω => fun ij : Fin (m n) × Fin n => A n ω ij.1 ij.2) ∧
    ProbabilityTheory.iIndepFun
      (fun ij : Fin (m n) × Fin n => fun ω => A n ω ij.1 ij.2) P ∧
    ∀ i j,
      (∫ ω, A n ω i j ∂P) = 0 ∧
      (∫ ω, (A n ω i j) ^ 2 ∂P) = variance n ∧
      ProbabilityTheory.HasSubgaussianMGF (fun ω => A n ω i j) (scale n) P

/-- The independent Gaussian component of a rectangular matrix. -/
def HasGaussianComponent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ → ℕ)
    (Atil G : ∀ n, Ω → Matrix (Fin (m n)) (Fin n) ℝ)
    (gvariance : ℕ → ℝ≥0) : Prop :=
  ∀ n,
    Measurable (fun ω => fun ij : Fin (m n) × Fin n => Atil n ω ij.1 ij.2) ∧
    Measurable (fun ω => fun ij : Fin (m n) × Fin n => G n ω ij.1 ij.2) ∧
    ProbabilityTheory.IndepFun
      (fun ω => fun ij : Fin (m n) × Fin n => Atil n ω ij.1 ij.2)
      (fun ω => fun ij : Fin (m n) × Fin n => G n ω ij.1 ij.2) P ∧
    ProbabilityTheory.iIndepFun
      (fun ij : Fin (m n) × Fin n => fun ω => G n ω ij.1 ij.2) P ∧
    ∀ i j,
      Measure.map (fun ω => G n ω i j) P =
        ProbabilityTheory.gaussianReal 0 (gvariance n)

/-- The two signal models in Theorem 8. In the first, a signal is deterministic and
the matrix entries are identically distributed. In the second, the signal has
independent, identically distributed coordinates independent of the matrix. -/
def TheoremEightSignal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ → ℕ)
    (A : ∀ n, Ω → Matrix (Fin (m n)) (Fin n) ℝ)
    (x0 : ∀ n, Ω → Fin n → ℝ) (δ ρ : ℝ) : Prop :=
  ( (∀ n i j i' j',
        Measure.map (fun ω => A n ω i j) P =
          Measure.map (fun ω => A n ω i' j') P) ∧
    ∃ v : ∀ n, Fin n → ℝ,
      (∀ n ω, x0 n ω = v n) ∧
      Tendsto (fun n =>
        ((Finset.univ.filter (fun i : Fin n => v n i ≠ 0)).card : ℝ) / (m n : ℝ))
        atTop (𝓝 ρ) ) ∨
  (∀ n,
      Measurable (fun ω => x0 n ω) ∧
      ProbabilityTheory.iIndepFun (fun i : Fin n => fun ω => x0 n ω i) P ∧
      ProbabilityTheory.IndepFun
        (fun ω => x0 n ω)
        (fun ω => fun ij : Fin (m n) × Fin n => A n ω ij.1 ij.2) P ∧
      (∀ i j,
        Measure.map (fun ω => x0 n ω i) P =
          Measure.map (fun ω => x0 n ω j) P) ∧
      ∀ i, (P {ω | x0 n ω i ≠ 0}).toReal = ρ * δ)

end AMPUniversality.Polytope


