-- Prove2me | Definitions.Def_JointMixND_QuadOT_Supplement_Elliptical
-- name    : JointMixND_QuadOT_Supplement_Elliptical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:09:47.346531+00:00
-- url     : https://prove2.me/theorems/e2bb1cbc-98ee-4583-a304-81dbbbf66e4b
-- title:
--   (16), pp. 16–17 — elliptical laws E_n(μ, Σ, ψ), non-degeneracy, the class E(ψ), Gaussian variance mixture families, Gaussian classes
-- statement:
--   Let $\psi:\mathbb R_+\to\mathbb R$, $\boldsymbol\mu\in\mathbb R^n$ and $\Sigma\in\mathbb R^{n\times n}$ symmetric positive semidefinite. A probability law $P$ on $\mathbb R^n$ is the **elliptical distribution** $\mathrm E_n(\boldsymbol\mu,\Sigma,\psi)$ if its characteristic function is
--
--   $$\varphi_P(\mathbf t)=\int e^{\mathrm i\,\mathbf t^\top\mathbf x}\,P(d\mathbf x)=\exp\big(\mathrm i\,\mathbf t^\top\boldsymbol\mu\big)\,\psi\big(\mathbf t^\top\Sigma\mathbf t\big),\qquad \mathbf t\in\mathbb R^n.\tag{16}$$
--
--   1. $P$ is **non-degenerate** if none of its marginals is a point mass.
--   2. The class $\mathcal E(\psi)$ consists of all non-degenerate elliptical laws with characteristic generator $\psi$, in every positive dimension $n\ge1$. "$\psi$ is a characteristic generator" is read as: $\mathcal E(\psi)$ has a member in a positive dimension.
--   3. $\mathcal E(\psi)$ is a **Gaussian variance mixture family** if there is a nonnegative random variable $W$ such that every member $\mathbf X$ satisfies $\mathbf X\overset d=\boldsymbol\mu+\sqrt W A\mathbf Z$ for some $\boldsymbol\mu\in\mathbb R^n$ and $A\in\mathbb R^{n\times k}$, where $\mathbf Z$ is a $k$-dimensional standard Gaussian vector independent of $W$.
--   4. $\mathcal E(\psi)$ is **Gaussian** if every member is a (multivariate) Gaussian law.
--
--   These objects carry Lemma 1 and Theorem 6, which characterize the elliptical families that contain negatively dependent joint mixes in every dimension.
--
--   **Formalization Note** $\psi$ is a function $\mathbb R\to\mathbb R$; only its values on $[0,\infty)$ enter, since $\mathbf t^\top\Sigma\mathbf t\ge0$. Symmetry of $\Sigma$ is part of `Matrix.PosSemidef`. The law of $\boldsymbol\mu+\sqrt W A\mathbf Z$ is the image of $\nu\otimes N(0,I_k)$, where $\nu$ is the law of $W$, a probability measure with $\nu((-\infty,0))=0$. "Gaussian" is Mathlib's `IsGaussian` (every continuous linear functional has a real Gaussian law, degenerate ones included). The reading of "characteristic generator" excludes $\psi\equiv1$ on $\mathbb R_+$, for which $\mathcal E(\psi)$ is empty; zero-dimensional laws are excluded from the class, so they cannot witness nonemptiness. See Theorem 6.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 16, (16); p. 17, non-degeneracy, the class E(ψ) and Gaussian variance mixture families; p. 18, Theorem 6

import Mathlib

namespace JointMixND.QuadOT.Supplement

open MeasureTheory ProbabilityTheory Matrix

/-- (16), p. 16: `P` is the elliptical law `E_n(μ, S, ψ)`: a probability law on `ℝⁿ` with
characteristic function `t ↦ exp(i tᵀμ) ψ(tᵀ S t)`, `S` symmetric positive semidefinite,
`ψ : ℝ₊ → ℝ` (values of `ψ` on negative reals are irrelevant). -/
def IsElliptical {n : ℕ} (ψ : ℝ → ℝ) (μ : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (P : Measure (Fin n → ℝ)) : Prop :=
  IsProbabilityMeasure P ∧ S.PosSemidef ∧
    ∀ t : Fin n → ℝ,
      ∫ x, Complex.exp (((∑ j, t j * x j : ℝ) : ℂ) * Complex.I) ∂P =
        Complex.exp (((∑ j, t j * μ j : ℝ) : ℂ) * Complex.I) * ((ψ (t ⬝ᵥ (S *ᵥ t)) : ℝ) : ℂ)

/-- p. 17: an elliptical law is non-degenerate if none of its marginals is a point mass. -/
def IsNondegenerate {n : ℕ} (P : Measure (Fin n → ℝ)) : Prop :=
  ∀ (i : Fin n) (a : ℝ), P.map (fun x => x i) ≠ Measure.dirac a

/-- p. 17: `P` belongs to the class `E(ψ)` (in dimension `n`): a non-degenerate elliptical law with
characteristic generator `ψ`, in a positive dimension. -/
def InClass {n : ℕ} (ψ : ℝ → ℝ) (P : Measure (Fin n → ℝ)) : Prop :=
  0 < n ∧ (∃ (μ : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ), IsElliptical ψ μ S P) ∧
    IsNondegenerate P

/-- "`ψ` is a characteristic generator" (Theorem 6, p. 17), read as: `E(ψ)` is nonempty, i.e. some
non-degenerate elliptical law of some positive dimension has generator `ψ`. -/
def HasNondegenerateMember (ψ : ℝ → ℝ) : Prop :=
  ∃ (n : ℕ) (P : Measure (Fin n → ℝ)), InClass ψ P

/-- The law of a `k`-dimensional standard Gaussian vector `Z`. -/
noncomputable def stdGaussianVec (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ : Fin k => gaussianReal 0 1)

/-- The law of `μ + √W A Z`, with `W ∼ ν` independent of the standard Gaussian `Z ∈ ℝᵏ`,
`μ ∈ ℝⁿ`, `A ∈ ℝ^{n×k}`. -/
noncomputable def gvmLaw {n k : ℕ} (ν : Measure ℝ) (μ : Fin n → ℝ) (A : Matrix (Fin n) (Fin k) ℝ) :
    Measure (Fin n → ℝ) :=
  (ν.prod (stdGaussianVec k)).map (fun p => μ + Real.sqrt p.1 • (A *ᵥ p.2))

/-- p. 17: `E(ψ)` is a Gaussian variance mixture family with mixing law `ν` (the law of a
nonnegative random variable `W`): every member `X` of `E(ψ)`, in every dimension, satisfies
`X =d μ + √W A Z` for some `μ`, `k`, `A`. -/
def IsGVMFamilyVia (ψ : ℝ → ℝ) (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ν (Set.Iio 0) = 0 ∧
    ∀ (n : ℕ) (P : Measure (Fin n → ℝ)), InClass ψ P →
      ∃ (μ : Fin n → ℝ) (k : ℕ) (A : Matrix (Fin n) (Fin k) ℝ), P = gvmLaw ν μ A

/-- p. 17: `E(ψ)` is a Gaussian variance mixture family (for some nonnegative `W`). -/
def IsGVMFamily (ψ : ℝ → ℝ) : Prop := ∃ ν : Measure ℝ, IsGVMFamilyVia ψ ν

/-- p. 18: the class `E(ψ)` is Gaussian: every member, in every dimension, is a Gaussian law. -/
def IsGaussianClass (ψ : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (P : Measure (Fin n → ℝ)), InClass ψ P → IsGaussian P

end JointMixND.QuadOT.Supplement


