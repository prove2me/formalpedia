-- Prove2me | Definitions.Def_McFadden1974_Asymptotics_LogitSample
-- name    : McFadden1974_Asymptotics_LogitSample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:24:52.762977+00:00
-- url     : https://prove2.me/theorems/a1f383ab-740f-4cf2-b6bc-cee79621003e
-- title:
--   §II–III and Appendix — serially indexed conditional logit sample, log-likelihood (44)–(45), Ω_m (47), Axioms 6–7, the MLE
-- statement:
--   This definition bundle sets up the large-sample model of McFadden (1974), §III and the Appendix, in the paper's **serial indexing** of trials and repetitions.
--
--   1. **Data.** Observation $m = 0, 1, 2, \dots$ has $J_m \ge 1$ alternatives, and alternative $i$ carries a vector of independent variables $z_{im} \in \mathbb R^K$.
--   2. **Selection probabilities (16).** For a parameter $\theta \in \mathbb R^K$,
--   $$P_{im}(\theta) = \frac{e^{z_{im}\theta}}{\sum_{j=1}^{J_m} e^{z_{jm}\theta}},$$
--   and $\bar z_m(\theta) = \sum_i P_{im}(\theta)\, z_{im}$ is the probability-weighted mean.
--   3. **Log-likelihood (44)–(45).** If $Y_m$ denotes the alternative chosen at observation $m$, the log-likelihood of the first $q$ observations is $L^q(\theta) = \sum_{m<q} \log P_{Y_m m}(\theta)$.
--   4. **Moment matrices (47).** $\Omega_m(\theta) = \sum_i P_{im}(\theta)\,(z_{im}-\bar z_m(\theta))(z_{im}-\bar z_m(\theta))'$.
--   5. **Axiom 6** for the first $q$ observations: the only $\gamma \in \mathbb R^K$ with $(z_{jm} - z_{Y_m m})\gamma \le 0$ for all $m<q$ and all $j$ is $\gamma = 0$.
--   6. **Axiom 7.** $J_m \le J_*$ and $|z_{im}| \le M$ for all $m, i$; and, with $\theta^0$ the true parameter,
--   $$\lim_{q\to\infty} \frac1q \sum_{m<q} \Omega_m(\theta^0) = \Omega$$
--   exists and is positive definite (Equations (27) and (48)).
--   7. **Sampling model.** On a probability space, the choices $Y_m$ are measurable, independent, and $\Pr(Y_m = i) = P_{im}(\theta^0)$.
--   8. **Maximum likelihood estimator.** A measurable selection $\hat\theta^q$ that maximizes $L^q$ whenever $L^q$ attains its maximum.
--   9. **$\Omega^{1/2}$ and $\Omega^{-1/2}$**, the positive semidefinite square root of $\Omega$ and its inverse, as linear maps of $\mathbb R^K$.
--
--   These are the objects of Lemmas 5 and 6, the existence, consistency and asymptotic normality of the conditional logit maximum likelihood estimator.
--
--   **Formalization Note** The paper's $N$ trials with $R_n$ repetitions are the special case in which consecutive observations carry equal data; the sample size $\sum_n R_n$ is $q$. The constant $C_q$ of (45) is $0$ (single draws). Vectors are in `EuclideanSpace ℝ (Fin K)` with the Euclidean norm (footnote 11's sum-of-absolute-values norm is equivalent). The maximum likelihood selection is arbitrary, but measurable, where no maximizer exists; measurability is an assumption on the estimator.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), pp. 113–115 (Axiom 4, Equations (16)–(18)), p. 116 (Axiom 6), pp. 119–120 (Axiom 7, Equation (27), footnote 11), p. 136 (Equations (44)–(48)); PDF pp. 9–12, 15–16, 32

import Mathlib

namespace McFadden1974.Asymptotics

/-! # The serially indexed conditional logit sample of the Appendix (definition bundle)

McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974): the model (16)–(18) of §II (pp. 113–115,
PDF pp. 9–11), Axioms 6 and 7 (p. 116 and pp. 119–120, PDF pp. 12, 15–16), and the serial
indexing of the Appendix, (44)–(48) (p. 136, PDF p. 32).

The Appendix (p. 136) writes "Let m be a serial index of trials and repetitions": observation
`m = 0, 1, 2, …` is one drawing from the alternative set of the trial it repeats. This bundle
indexes the data that way. Observation `m` has `J m ≥ 1` alternatives with attribute vectors
`z m i ∈ ℝ^K` (the paper's `z_{i n_m}`), the parameter is `θ ∈ ℝ^K`, and a sample of size `q`
is the first `q` observations.

Formalization Note: the paper's experiment ("N distinct trials (s_n, B_n)" with "R_n repetitions
of trial n", pp. 113–114) is the special case in which consecutive observations carry the same
data `J m`, `z m`; the sample size `Σ_{n=1}^N R_n` is `q`, and "`Σ R_n → +∞`" is `q → ∞`. The
serial model is slightly more general (the data of observation `m` need not repeat), and the
paper's own proofs of Lemmas 5 and 6 work in it. Vectors live in `EuclideanSpace ℝ (Fin K)`,
`z θ` of the paper is the inner product `⟪z, θ⟫`, and `|·|` is the Euclidean norm. Bundle choice:
one module holds the data, the probabilities (16), the log-likelihood (44)–(45), the matrices
(47), Axioms 6 and 7, the sampling model and the maximum likelihood selection, because every
statement of the mission uses all of them together. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder

/-- **The data of a serially indexed sample** (pp. 113–114 and p. 136). Observation `m` has
`J m` alternatives, `J m ≥ 1`, and alternative `i : Fin (J m)` has the vector of independent
variables `z m i ∈ ℝ^K` (the paper's `z_{in} = (v^1(s_n, x_{in}), …, v^K(s_n, x_{in}))` of
Axiom 4, p. 113, for the trial `n = n_m` that observation `m` repeats).

Formalization Note: alternatives are indexed by `Fin (J m)`, i.e. `0, …, J m − 1` for the paper's
`1, …, J_n`. `one_le_J` makes every alternative set nonempty, so a choice can be drawn. -/
structure SerialData (K : ℕ) where
  /-- number of alternatives `J_{n_m}` of observation `m` -/
  J : ℕ → ℕ
  /-- independent variables `z_{i n_m}` -/
  z : (m : ℕ) → Fin (J m) → EuclideanSpace ℝ (Fin K)
  /-- every alternative set is nonempty -/
  one_le_J : ∀ m, 1 ≤ J m

variable {K : ℕ}

/-- **Equation (16)** (p. 113, PDF p. 9): the conditional logit selection probability
`P_{in}(θ) = e^{z_{in} θ} / Σ_{j=1}^{J_n} e^{z_{jn} θ}` of alternative `i` at observation `m`. -/
noncomputable def prob (D : SerialData K) (m : ℕ) (i : Fin (D.J m))
    (θ : EuclideanSpace ℝ (Fin K)) : ℝ :=
  Real.exp (inner ℝ (D.z m i) θ) / ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ)

/-- **The probability-weighted mean** `z̄_n = Σ_{i=1}^{J_n} z_{in} P_{in}` (p. 115, PDF p. 11,
below (20)), at observation `m` and parameter `θ`. -/
noncomputable def zbar (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) :
    EuclideanSpace ℝ (Fin K) :=
  ∑ i : Fin (D.J m), prob D m i θ • D.z m i

/-- **Equations (44)–(45)** (p. 136, PDF p. 32): the log-likelihood of the first `q`
observations, `L^q(θ) = Σ_{m=1}^{q} λ^m(θ)` with `λ^m(θ) = Σ_i S_{im} log P_{in_m}(θ)`, where
`Y m ω` is the alternative chosen at observation `m` in the outcome `ω` (so `S_{im} = 1` exactly
for `i = Y m ω`).

Formalization Note: the paper's constant `C_q` of (45) is `0` here. It is the multinomial
coefficient term of (18), which vanishes for single draws; it does not depend on `θ`, so the
maximizers are unaffected. Observations are numbered from `0`, so the first `q` are
`Finset.range q`. Every `P_{in}(θ)` is positive, so `Real.log` is applied to positive numbers
only. -/
noncomputable def logLik {Ω : Type*} (D : SerialData K) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (q : ℕ) (θ : EuclideanSpace ℝ (Fin K)) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range q, Real.log (prob D m (Y m ω) θ)

/-- **Equation (47)** (p. 136, PDF p. 32): the per-observation moment matrix
`Ω_m = Σ_{i=1}^{J_{n_m}} (z_{in_m} − z̄_{n_m})' P_{in_m} (z_{in_m} − z̄_{n_m})`, evaluated at
the parameter `θ` (the paper evaluates it at the true value `θ⁰`).

Formalization Note: `(z − z̄)'(z − z̄)` is the outer product `Matrix.vecMulVec`, a `K × K`
matrix; vectors are taken as coordinate functions via `WithLp.ofLp`. -/
noncomputable def momentMatrix (D : SerialData K) (θ : EuclideanSpace ℝ (Fin K)) (m : ℕ) :
    Matrix (Fin K) (Fin K) ℝ :=
  ∑ i : Fin (D.J m), prob D m i θ •
    Matrix.vecMulVec (WithLp.ofLp (D.z m i - zbar D m θ)) (WithLp.ofLp (D.z m i - zbar D m θ))

/-- **Axiom 6 for the first `q` observations** (p. 116, PDF p. 12): "There exists no nonzero
K-vector γ satisfying `S_{in}(z_{jn} − z_{in})γ ≤ 0` for i, j = 1, …, J_n and n = 1, …, N."

Formalization Note: in the serial indexing `S_{im}` is `1` for the chosen alternative
`i = Y m ω` and `0` otherwise, so the inequalities with `S_{im} = 0` are trivially true and the
condition reads: every `γ` with `⟪z_{jm} − z_{Y_m m}, γ⟫ ≤ 0` for all observations `m < q` and
all alternatives `j` is `0`. It depends on the outcome `ω`, because the choices are random. -/
def Axiom6 {Ω : Type*} (D : SerialData K) (Y : (m : ℕ) → Ω → Fin (D.J m)) (q : ℕ)
    (ω : Ω) : Prop :=
  ∀ γ : EuclideanSpace ℝ (Fin K),
    (∀ m < q, ∀ j : Fin (D.J m), inner ℝ (D.z m j - D.z m (Y m ω)) γ ≤ 0) → γ = 0

/-- **The boundedness part of Axiom 7** (p. 119–120, PDF pp. 15–16): "The numbers of
alternatives J_n are uniformly bounded by an integer J_*. The independent variables z_in are
uniformly bounded by a scalar M."

Formalization Note: footnote 11 measures `|z_in|` by the sum of absolute values of the entries;
this formalization uses the Euclidean norm `‖z m i‖`. The two norms are equivalent (with
constants depending only on `K`) and Axiom 7's bound is qualitative; the constants `2M`, `4M²`,
`8M³` of (43) and `e^{2M|θ|}` of (42) remain valid with Euclidean norms on `z`, `θ` and operator
norms on derivatives. Both bounds are uniform over all observations. -/
structure IsBounded (D : SerialData K) (Jstar : ℕ) (M : ℝ) : Prop where
  J_le : ∀ m, D.J m ≤ Jstar
  norm_z_le : ∀ m (i : Fin (D.J m)), ‖D.z m i‖ ≤ M

/-- **Axiom 7** (pp. 119–120, PDF pp. 15–16) in the serial indexing of the Appendix: the
boundedness of `J_n` and `z_in`, and "The limit of the weighted moment matrix, as
Σ_{n=1}^N R_n → +∞,
(27) lim (Σ_{n=1}^N R_n)^{−1} Σ_{n=1}^N R_n Σ_{i=1}^{J_n} (z_in − z̄_n)' P_in (z_in − z̄_n) = Ω,
exists and is positive-definite."

Formalization Note: in the serial indexing the weighted average of (27) is the plain average
`(1/q) Σ_{m<q} Ω_m` of the matrices (47), which is Equation (48) (p. 136): "Then by Axiom 7,
lim_{q→∞} (1/q) Σ_{m=1}^{q} Ω_m = Ω." The selection probabilities in (27) are evaluated at the
true parameter `θ⁰`, as (47) makes explicit; the paper's last factor `(z_in − z̄_in)` in (27) is a
misprint for `(z_in − z̄_n)`. The limit is entrywise (the topology of `Matrix`), and `Ωlim` is
positive definite. -/
structure Axiom7 (D : SerialData K) (Jstar : ℕ) (M : ℝ) (θ₀ : EuclideanSpace ℝ (Fin K))
    (Ωlim : Matrix (Fin K) (Fin K) ℝ) : Prop where
  bounded : IsBounded D Jstar M
  tendsto_avg : Tendsto
    (fun q : ℕ => (q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, momentMatrix D θ₀ m) atTop (𝓝 Ωlim)
  posDef : Ωlim.PosDef

/-- **The sampling model** (pp. 114–115, PDF pp. 10–11, and p. 136, PDF p. 32): on a probability
space `(Ω, μ)` the choices `Y m : Ω → Fin (J m)` are measurable and independent, and the choice
at observation `m` is a drawing from the selection probabilities (16) at the true parameter
vector `θ⁰`: `μ(Y_m = i) = P_{in_m}(θ⁰)`.

Formalization Note: this is the paper's "drawings from a multinomial distribution with
probabilities given by Equation (16)" (p. 115) and its "sequence of independent random variables"
(44) (p. 136), with `θ⁰` "the true parameter vector" of Lemma 6. Independence across all
observations, repetitions of one trial included, is `iIndepFun`. -/
structure IsLogitSample {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (D : SerialData K)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Y : (m : ℕ) → Ω → Fin (D.J m)) : Prop where
  measurable : ∀ m, Measurable (Y m)
  indep : iIndepFun Y μ
  law : ∀ m (i : Fin (D.J m)), μ (Y m ⁻¹' {i}) = ENNReal.ofReal (prob D m i θ₀)

/-- **The maximum likelihood estimator** `θ̂^q` (p. 115, PDF p. 11: "a vector θ̂, depending on the
observations, which maximizes the likelihood (18) of the given sample"), as a selection.

Formalization Note: a maximizer of `L^q(·, ω)` need not exist (p. 116: "there is a positive
probability that Axiom 6 may fail in a finite sample"), and need not be unique when Axiom 5
fails. `IsMLE` requires `θhat q ω` to be a maximizer of `L^q(·, ω)` whenever one exists, and
leaves it arbitrary otherwise; Lemma 5 shows that the exceptional event is asymptotically
negligible. `θhat q` is required to be measurable: this is an assumption on the estimator, not on
the paper's model, and without it the law of `θ̂^q` is undefined. -/
structure IsMLE {Ω : Type*} [MeasurableSpace Ω] (D : SerialData K)
    (Y : (m : ℕ) → Ω → Fin (D.J m))
    (θhat : ℕ → Ω → EuclideanSpace ℝ (Fin K)) : Prop where
  measurable : ∀ q, Measurable (θhat q)
  isMax : ∀ q ω, (∃ θ, ∀ θ', logLik D Y q θ' ω ≤ logLik D Y q θ ω) →
    ∀ θ', logLik D Y q θ' ω ≤ logLik D Y q (θhat q ω) ω

/-- **`Ω^{1/2}`** (p. 120, PDF p. 16, Equation (28), and p. 135): the positive semidefinite square
root of the matrix `Ω` of Axiom 7, as a linear map on `ℝ^K`.

Formalization Note: `CFC.sqrt` is the continuous functional calculus square root in the matrix
order (`open scoped MatrixOrder`); for a positive semidefinite matrix it is the unique positive
semidefinite matrix whose square is `Ω`. It acts on `EuclideanSpace ℝ (Fin K)` through
`Matrix.toEuclideanLin`. -/
noncomputable def sqrtMap (Ωlim : Matrix (Fin K) (Fin K) ℝ) :
    EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (Fin K) :=
  Matrix.toEuclideanLin (CFC.sqrt Ωlim)

/-- **`Ω^{−1/2}`** (p. 137, PDF p. 33, Equation (58)): the inverse of the positive semidefinite
square root of `Ω`, as a linear map on `ℝ^K`.

Formalization Note: the matrix inverse `(CFC.sqrt Ω)⁻¹` (`Matrix.inv`); for positive definite
`Ω`, which Axiom 7 assumes, `CFC.sqrt Ω` is invertible and this is the true inverse. -/
noncomputable def invSqrtMap (Ωlim : Matrix (Fin K) (Fin K) ℝ) :
    EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (Fin K) :=
  Matrix.toEuclideanLin (CFC.sqrt Ωlim)⁻¹

end McFadden1974.Asymptotics


