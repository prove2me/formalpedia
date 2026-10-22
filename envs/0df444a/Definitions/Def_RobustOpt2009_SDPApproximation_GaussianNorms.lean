-- Prove2me | Definitions.Def_RobustOpt2009_SDPApproximation_GaussianNorms
-- name    : RobustOpt2009_SDPApproximation_GaussianNorms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:08.74124+00:00
-- url     : https://prove2.me/theorems/667ac0ef-803f-41a8-a3f6-e75ebee478a3
-- title:
--   Standard Gaussian laws and Euclidean/Frobenius norm products
-- statement:
--   A real standard Gaussian vector has independent $N(0,1)$ coordinates. A complex standard Gaussian vector has independent real and imaginary parts, each distributed as $N(0,1/2)$; hence its complex covariance matrix is the identity.
--
--   For a real or complex vector, the Euclidean norm is $(\sum_i|x_i|^2)^{1/2}$. For a matrix, the Frobenius norm is $(\sum_{i,j}|M_{ij}|^2)^{1/2}$. Given compatible matrices $L,R$, the norm product is
--   $$x\longmapsto\|Lx\|_2\|Rx\|_2.$$
--   These quantities specify the expectations in Proposition B.4.12 without confusing the Frobenius matrix norm with the uncertainty blocks' operator norm.
--
--   **Formalization Note** Real laws are finite products of Mathlib's Gaussian measures. Complex expectations are integrated on pairs of real coordinates, interpreted as real and imaginary parts, against the product law with variance $1/2$ in each part. No measure is formed by mapping a potentially nonmeasurable function.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Appendix B.4.4.2, printed p. 499 (PDF p. 525), and Proposition B.4.12, printed p. 502 (PDF p. 528)

import Mathlib

open Matrix MeasureTheory ProbabilityTheory

namespace RobustOpt2009.SDPApproximation

/-- Independent real standard normal coordinates. -/
noncomputable def realGaussian (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- Independent real and imaginary parts of variance one half, so each
complex coordinate has complex variance one (Appendix B, printed p. 499). -/
noncomputable def complexGaussianInput (n : ℕ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi fun _ => (gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))

def complexVector {n : ℕ} (x : Fin n → ℝ × ℝ) : Fin n → ℂ :=
  fun i => ⟨(x i).1, (x i).2⟩

/-- Euclidean vector norm, written explicitly to avoid the sup norm on Pi types. -/
noncomputable def euclideanReal {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

noncomputable def euclideanComplex {n : ℕ} (x : Fin n → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- Frobenius, not operator, matrix norm in (B.4.35) and (B.4.36). -/
noncomputable def frobeniusReal {p n : ℕ} (L : Matrix (Fin p) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (L i j) ^ 2)

noncomputable def frobeniusComplex {p n : ℕ} (L : Matrix (Fin p) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖L i j‖ ^ 2)

noncomputable def realNormProduct {p q n : ℕ}
    (L : Matrix (Fin p) (Fin n) ℝ) (R : Matrix (Fin q) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  euclideanReal (L *ᵥ x) * euclideanReal (R *ᵥ x)

noncomputable def complexNormProduct {p q n : ℕ}
    (L : Matrix (Fin p) (Fin n) ℂ) (R : Matrix (Fin q) (Fin n) ℂ)
    (x : Fin n → ℝ × ℝ) : ℝ :=
  euclideanComplex (L *ᵥ complexVector x) * euclideanComplex (R *ᵥ complexVector x)

end RobustOpt2009.SDPApproximation


