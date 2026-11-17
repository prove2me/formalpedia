-- Prove2me | Definitions.Def_PhiSobBayes_Supplement_labelJoint
-- name    : PhiSobBayes_Supplement_labelJoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:44:02.396188+00:00
-- url     : https://prove2.me/theorems/e7b3ab8d-714d-481f-8399-61f0fae5e53e
-- title:
--   Randomized binary label: the joint law of $(U, X, Y_s)$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^n$, let $p:\mathbb R^n\to[0,1]$ be measurable and let $s\ge 0$. The **label joint law** $\mathsf L_{\mu,p,s}$ is the law of the triple $(U,X,Y_s)$ in which $X\sim\mu$, the binary label $U\in\{0,1\}$ satisfies $\mathbb P(U=1\mid X)=p(X)$, and $Y_s=\sqrt s\,X+G$ with $G\sim\gamma_n=N(0,I_n)$ independent of $(U,X)$:
--
--   $$
--   (U,X,Y_s)\sim \mu(\mathrm dx)\,\mathrm{Bernoulli}(p(x))(\mathrm du)\,N(\sqrt s\,x,I_n)(\mathrm dy).
--   $$
--
--   In the paper's language (Definition 6), $U$ is a **randomized binary label** of $X$: $\mathbb P(U=1\mid X)$ is a measurable function of $X$ and $U-X-Y_s$ is a Markov chain ($U$ and $Y_s$ are conditionally independent given $X$). Every randomized binary label has a joint law of this form, and every such law comes from one, so quantifying over measurable $p$ with values in $[0,1]$ is quantifying over randomized binary labels. The mutual informations $I(U;X)$ and $I(U;X\mid Y_s)$ of Theorems 4.6 and 4.9 are computed under this law.
--
--   **Formalization Note** The label `true` stands for $U=1$. The law is the pushforward of $\mu\otimes\mathrm{Unif}[0,1]\otimes\gamma_n$ by $(x,v,g)\mapsto(\mathbf 1[v<p(x)],\,x,\,\sqrt s\,x+g)$, with $\gamma_n$ Mathlib's `stdGaussian`. The label, signal and observation are the coordinates `ω.1`, `ω.2.1`, `ω.2.2`. The module also records that the law is a finite measure when $\mu$ is.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 6, p.17 (PDF 17); Definition 15, p.58 (PDF 58); Definition 4, p.14 (PDF 14)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PhiSobBayes.Supplement

/-- The **joint law of a randomized binary label, the signal and the GAM observation**:
the law of `(U, X, Y_s)` where `X ∼ μ`, `ℙ(U = 1 | X) = p(X)`, and `Y_s = √s X + G` with
`G ∼ N(0, I_n)` independent of `(U, X)`. Concretely,
`(U, X, Y_s) ∼ μ(dx) · Bernoulli(p(x))(du) · N(√s x, I_n)(dy)`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027
submission (held version, sha256 5ea05e95…8ed487), Definition 6, p.17 (PDF 17): "a randomized binary
label of 𝑋 is a random variable 𝑈 ∈ {0, 1} such that ℙ(𝑈 = 1 | 𝑋) is a measurable function of 𝑋 and the
sequence 𝑈 − 𝑋 − 𝑌𝑡 is a Markov chain"; Markov chain as in Definition 15, p.58 (PDF 58); the GAM of
Definition 4, p.14 (PDF 14).

**Formalization Note** The label is `true` for `U = 1`. The law is the pushforward of
`μ ⊗ Unif[0, 1] ⊗ γ_n` (with `γ_n` Mathlib's `stdGaussian`) by
`(x, v, g) ↦ (v < p(x), x, √s x + g)`, so `ℙ(U = 1 | X = x) = p(x)` and `U ⊥ Y_s | X`. For a
measurable `p : ℝⁿ → [0, 1]` this is exactly the law of `(U, X, Y_s)` for a randomized binary label
`U` with `ℙ(U = 1 | X) = p(X)`, and every randomized binary label has a joint law of this form; the
theorems only involve this joint law. Every theorem using it assumes `p` measurable with values in
`[0, 1]` (for a non-measurable `p`, `Measure.map` returns `0`). The signal is coordinate `ω.2.1`,
the observation `ω.2.2`, the label `ω.1`. -/
noncomputable def labelJoint {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (p : EuclideanSpace ℝ (Fin n) → ℝ) (s : ℝ) :
    Measure (Bool × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  ((μ.prod (volume : Measure unitInterval)).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
    (fun z => (decide (((z.1.2 : unitInterval) : ℝ) < p z.1.1), z.1.1, Real.sqrt s • z.1.1 + z.2))

/-- `labelJoint μ p s` is a finite measure whenever `μ` is (it is a pushforward of a product of
finite measures). -/
instance labelJoint.instIsFiniteMeasure {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsFiniteMeasure μ] (p : EuclideanSpace ℝ (Fin n) → ℝ) (s : ℝ) :
    IsFiniteMeasure (labelJoint μ p s) := by
  unfold labelJoint; infer_instance

end PhiSobBayes.Supplement


