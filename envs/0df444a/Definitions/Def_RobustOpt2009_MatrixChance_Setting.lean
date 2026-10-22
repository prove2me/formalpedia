-- Prove2me | Definitions.Def_RobustOpt2009_MatrixChance_Setting
-- name    : RobustOpt2009_MatrixChance_Setting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:08.661627+00:00
-- url     : https://prove2.me/theorems/912f7099-0e10-448c-96c1-e25c23bde163
-- title:
--   Section 10.1 — matrix chance constraints and Gaussian tail conventions
-- statement:
--   Let $A,B_1,\ldots,B_L$ be real square matrices. This module defines the linear perturbation $S_B(z)=\sum_\ell z_\ell B_\ell$, its Euclidean operator norm, and the two-sided matrix event $-tA\preceq S\preceq tA$, where each order inequality means that its difference is positive semidefinite. The variance certificate is
--   $$\exists Y_1,\ldots,Y_L:\quad \begin{pmatrix}Y_\ell&B_\ell\\B_\ell&A\end{pmatrix}\succeq0\ (1\le\ell\le L),\qquad \sum_\ell Y_\ell\preceq A.$$
--   For measurable real random variables, A.I means $|\zeta_\ell|\le1$ almost surely and $\mathbb E\zeta_\ell=0$; A.II means that each coordinate has law $N(0,1)$. Independence, measurability, symmetry, and a probability measure are imposed by the using theorems, not concealed in the certificate.
--
--   The upper normal tail $T$ and its extended inverse $q$ are concrete functions of the standard Gaussian measure. The auxiliary envelope is $H(t)=e^{-t^2/2}$ on finite arguments and $H(\pm\infty)=0$. The amplification argument is
--   $$a(\chi,\Upsilon,\Omega)=q(1-\chi)+(\Omega-\Upsilon)\max\{1,\Upsilon^{-1}q(1-\chi)\}.$$
--   These definitions specify the objects used in both concentration branches and the block-matrix goal. The raw definitions allow zero-dimensional matrices; the theorem statements assume positive dimensions.
--
--   **Formalization Note** Matrices and perturbation coordinates have positive finite dimensions, indexed from zero in Lean. Probabilities are real values of probability measures. The function $T(t)=\Pr\{G>t\}$ for $G\sim N(0,1)$ is the book's upper-tail Erf, not the usual error function. Its quantile $q(p)=\inf\{t\in\overline{\mathbb R}:T(t)\le p\}$ is extended by $q(0)=+\infty$ and $q(1)=-\infty$; $T(+\infty)=0$ and $e^{-\infty^2/2}=0$. This makes the probability-one endpoint, not specified by (2.3.22), explicit without removing it. Finite arguments give exactly the displayed source formulas.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Section 10.1, printed pp. 237–241 (PDF pp. 263–267); equation (2.3.22), printed p. 39 (PDF p. 65); Appendix B.5, printed p. 508 (PDF p. 534).

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RobustOpt2009.MatrixChance

/-- Upper standard normal tail, extended to infinite thresholds by the event itself. -/
noncomputable def normalTail (t : EReal) : ℝ :=
  ((gaussianReal 0 1) {x : ℝ | t < (x : EReal)}).toReal

/-- The upper-tail quantile; at p=0 it is +∞, and at p=1 it is -∞. -/
noncomputable def tailQuantile (p : ℝ) : EReal :=
  sInf {t : EReal | normalTail t ≤ p}

/-- exp(-t²/2), with its limiting value zero at either infinite endpoint. -/
noncomputable def gaussianEnvelope (t : EReal) : ℝ :=
  if t = ⊤ ∨ t = ⊥ then 0 else Real.exp (-(t.toReal ^ 2) / 2)

/-- The Gaussian confidence-amplification argument in (10.1.12) and (10.1.16). -/
noncomputable def amplificationArgument (χ Υ Ω : ℝ) : EReal :=
  tailQuantile (1 - χ) + ((Ω - Υ : ℝ) : EReal) *
    max 1 (((Υ⁻¹ : ℝ) : EReal) * tailQuantile (1 - χ))

/-- Euclidean operator norm, not the entrywise or row-sum matrix norm. -/
noncomputable def spectralNorm {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖

/-- The linear matrix perturbation. -/
def perturbation {m L : ℕ} (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (z : Fin L → ℝ) : Matrix (Fin m) (Fin m) ℝ := ∑ l, z l • B l

/-- The two Loewner inequalities -t A ≤ S ≤ t A. -/
def sandwich {m : ℕ} (A S : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) : Prop :=
  (S + t • A).PosSemidef ∧ (t • A - S).PosSemidef

/-- Block positive-semidefinite certificate (10.1.13). -/
def varianceCertificate {m L : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Fin L → Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∃ Y : Fin L → Matrix (Fin m) (Fin m) ℝ,
    (∀ l, (Matrix.fromBlocks (Y l) (B l) (B l) A).PosSemidef) ∧
      (A - ∑ l, Y l).PosSemidef

/-- A.I, with the zero mean stipulated at the start of Section 10.1. -/
def boundedCase {W : Type*} [MeasurableSpace W] {L : ℕ}
    (μ : Measure W) (ζ : Fin L → W → ℝ) : Prop :=
  ∀ l, (∀ᵐ w ∂μ, |ζ l w| ≤ 1) ∧ (∫ w, ζ l w ∂μ) = 0

/-- A.II: every coordinate has the standard normal law. Measurability is a theorem premise. -/
def gaussianCase {W : Type*} [MeasurableSpace W] {L : ℕ}
    (μ : Measure W) (ζ : Fin L → W → ℝ) : Prop :=
  ∀ l, μ.map (ζ l) = gaussianReal 0 1

end RobustOpt2009.MatrixChance


