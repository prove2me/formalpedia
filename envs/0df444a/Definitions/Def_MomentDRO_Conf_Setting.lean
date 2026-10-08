-- Prove2me | Definitions.Def_MomentDRO_Conf_Setting
-- name    : MomentDRO_Conf_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:45:25.609624+00:00
-- url     : https://prove2.me/theorems/ea5efacd-de65-43c5-9933-c9a139b9c8cc
-- title:
--   §4, pp. 9–13 — moments, independent samples, empirical estimators, and confidence constants
-- statement:
--   Let $P$ be a probability distribution on $\mathbb R^m$ with finite second moments. Its mean is $\mu=\mathbb E_P[\xi]$, its second moment about $c$ is $\mathbb E_P[(\xi-c)(\xi-c)^\mathsf T]$, and its covariance is $\Sigma=\mathbb E_P[(\xi-\mu)(\xi-\mu)^\mathsf T]$. A sample $S=(\xi_1,\ldots,\xi_M)$ has the product law $P^M$.
--
--   The empirical mean and covariance used in §4 are
--   $$\widehat\mu=\frac1M\sum_i\xi_i,\qquad \widehat\Sigma=\frac1M\sum_i(\xi_i-\widehat\mu)(\xi_i-\widehat\mu)^\mathsf T.$$
--   The covariance estimate centred at a known mean $c$ uses the same factor $1/M$ with $c$ in place of $\widehat\mu$. The bound also uses $\alpha(t)=\frac{R^2}{\sqrt M}(\sqrt{1-m/R^4}+\sqrt{\log(1/t)})$ and $\beta(t)=\frac{R^2}{M}(2+\sqrt{2\log(1/t)})^2$.
--
--   Assumption 4 means $R\ge0$ and $(\xi-\mu)^\mathsf T\Sigma^{-1}(\xi-\mu)\le R^2$ almost surely. The normalized case has mean zero, covariance $I$, and Euclidean squared length at most $R^2$ almost surely. Matrix comparison $A\preceq B$ means $B-A$ is positive semidefinite. These definitions are shared by the chapter's mean and covariance results.
--
--   **Formalization Note** Coordinates have finite $L^2$ moments, ensuring the stated real integrals are genuine. Vectors are functions on `Fin m`; Euclidean squared length uses their dot product. The Loewner order reuses the published `HighDimStat.RandomMatrices.LoewnerLE` predicate. At $M=0$ the empirical formulas use Lean's total inverse, but every statistical theorem assumes a positive sample size.
-- source:
--   Delage & Ye, Distributionally robust optimization under moment uncertainty with application to data-driven problems, authors' draft of 20 Feb 2008 (OR 58(3), 2010), pp. 9–13, §4, Assumption 4, (8), (10), (12)

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_LoewnerLE

namespace MomentDRO.Conf

open MeasureTheory
open scoped BigOperators

noncomputable def quadForm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (v : Fin m → ℝ) : ℝ := dotProduct v (Matrix.mulVec A v)

export HighDimStat.RandomMatrices (LoewnerLE)

def HasSecondMoments {m : ℕ} (P : Measure (Fin m → ℝ)) : Prop :=
  IsProbabilityMeasure P ∧ ∀ i : Fin m, MemLp (fun ξ : Fin m → ℝ => ξ i) 2 P

noncomputable def meanVec {m : ℕ} (P : Measure (Fin m → ℝ)) : Fin m → ℝ :=
  fun i => ∫ ξ, ξ i ∂P

noncomputable def secondMomentAbout {m : ℕ} (P : Measure (Fin m → ℝ))
    (c : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => ∫ ξ, (ξ i - c i) * (ξ j - c j) ∂P

noncomputable def covMat {m : ℕ} (P : Measure (Fin m → ℝ)) :
    Matrix (Fin m) (Fin m) ℝ := secondMomentAbout P (meanVec P)

noncomputable def sampleLaw {m : ℕ} (P : Measure (Fin m → ℝ)) (M : ℕ) :
    Measure (Fin M → (Fin m → ℝ)) := Measure.pi (fun _ : Fin M => P)

noncomputable def empMean {m M : ℕ} (S : Fin M → (Fin m → ℝ)) : Fin m → ℝ :=
  (M : ℝ)⁻¹ • ∑ i, S i

noncomputable def empCovAbout {m M : ℕ} (S : Fin M → (Fin m → ℝ))
    (c : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (M : ℝ)⁻¹ • ∑ i, Matrix.vecMulVec (S i - c) (S i - c)

noncomputable def empCov {m M : ℕ} (S : Fin M → (Fin m → ℝ)) :
    Matrix (Fin m) (Fin m) ℝ := empCovAbout S (empMean S)

noncomputable def alphaC (M m : ℕ) (R t : ℝ) : ℝ :=
  R ^ 2 / Real.sqrt M *
    (Real.sqrt (1 - (m : ℝ) / R ^ 4) + Real.sqrt (Real.log (1 / t)))

noncomputable def betaC (M : ℕ) (R t : ℝ) : ℝ :=
  R ^ 2 / (M : ℝ) * (2 + Real.sqrt (2 * Real.log (1 / t))) ^ 2

def Assumption4 {m : ℕ} (P : Measure (Fin m → ℝ)) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ᵐ ξ ∂P, quadForm (covMat P)⁻¹ (ξ - meanVec P) ≤ R ^ 2

def IsNormalized {m : ℕ} (Pζ : Measure (Fin m → ℝ)) (R : ℝ) : Prop :=
  HasSecondMoments Pζ ∧ meanVec Pζ = 0 ∧ secondMomentAbout Pζ 0 = 1 ∧
    0 ≤ R ∧ ∀ᵐ ζ ∂Pζ, ζ ⬝ᵥ ζ ≤ R ^ 2

end MomentDRO.Conf


