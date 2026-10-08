-- Prove2me | Definitions.Def_McFadden1974_MLE_Model
-- name    : McFadden1974_MLE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:44:29.30929+00:00
-- url     : https://prove2.me/theorems/bd679568-5a66-4ee7-8d77-2ca11aef3a8e
-- title:
--   Axiom 4, Equations (16)–(20) — conditional logit data, selection probabilities, log-likelihood, gradient and Hessian
-- statement:
--   A **conditional logit choice experiment** with $K$ parameters consists of $N \ge 1$ trials. Trial $n$ offers an alternative set of $J_n$ alternatives $i = 1,\dots,J_n$, with attribute vectors $z_{in} \in \mathbb{R}^K$ (the values $z^k_{in} = v^k(s_n, x_{in})$ of the specified functions of Axiom 4). Trial $n$ is repeated $R_n$ times and alternative $i$ is chosen $S_{in}$ times, so that
--   $$R_n = \sum_{j=1}^{J_n} S_{jn}.$$
--   Every trial is observed at least once: $R_n \ge 1$ for all $n$.
--
--   For a parameter $\theta \in \mathbb{R}^K$ (with $z_{in}\theta$ the inner product), the definitions are:
--
--   1. the **selection probabilities** (16)
--   $$P_{in}(\theta) = \frac{e^{z_{in}\theta}}{\sum_{j=1}^{J_n} e^{z_{jn}\theta}};$$
--   2. the mean attribute vector $\bar z_n(\theta) = \sum_{i=1}^{J_n} z_{in} P_{in}(\theta)$;
--   3. the constant $C = \sum_{n=1}^N \big[\log R_n! - \sum_{j=1}^{J_n} \log S_{jn}!\big]$;
--   4. the **log-likelihood** (18)
--   $$L(\theta) = C - \sum_{n=1}^N \sum_{i=1}^{J_n} S_{in} \log \sum_{j=1}^{J_n} e^{(z_{jn}-z_{in})\theta};$$
--   5. the vector of (19), $\sum_{n=1}^N \sum_{j=1}^{J_n} (S_{jn} - R_n P_{jn}(\theta))\, z_{jn}$;
--   6. the symmetric linear map of (20), $\gamma \mapsto -\sum_{n=1}^N R_n \sum_{j=1}^{J_n} P_{jn}(\theta)\,\langle z_{jn} - \bar z_n, \gamma\rangle\,(z_{jn} - \bar z_n)$, whose matrix is $-\sum_n R_n \sum_j (z_{jn}-\bar z_n)' P_{jn} (z_{jn}-\bar z_n)$.
--
--   These are the objects of McFadden's maximum likelihood analysis of the conditional logit model; Axioms 1–4 are built in through the logit form (16).
--
--   **Formalization Note** Trials and alternatives are indexed from $0$ (`Fin N`, `Fin (J n)`); $\mathbb{R}^K$ is `EuclideanSpace ℝ (Fin K)`, so norms are Euclidean. The requirements $N \ge 1$ and $R_n \ge 1$ are fields of the data structure. The logarithm in $L$ is of a sum containing the term $e^0 = 1$, so it is always of a number $\ge 1$.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), pp. 113-115 (PDF pp. 9-11), Axiom 4 and Equations (16)-(20)

import Mathlib

/-!
# McFadden (1974), §II — the conditional logit model (16)–(20)

Definition bundle: the data of a choice experiment, the selection probabilities (16), the constant
`C` and the log-likelihood (18), its gradient (19) and its Hessian (20).

McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), pp. 113–115 (PDF pp. 9–11), Axiom 4 and
Equations (16)–(20).
-/

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

/-- **Data of a conditional logit choice experiment** (McFadden 1974, Axiom 4 and the paragraphs
after it, pp. 113–114, PDF pp. 9–10).

There are `N` distinct trials `(s_n, B_n)`, `n = 1, …, N`. The alternative set `B_n` of trial `n`
has `J n` alternatives `i = 1, …, J_n`, with attribute vectors `z n i = z_in ∈ ℝ^K`
(`z_in^k = v^k(s_n, x_in)`). Trial `n` is repeated `R_n` times, and alternative `i` is observed to
be chosen `S n i = S_in` times, so `R_n = ∑_i S_in`.

**Formalization Note.** Trials and alternatives are indexed by `Fin N` and `Fin (J n)` (0-based).
The attribute vectors live in `EuclideanSpace ℝ (Fin K)`, so `z_in θ` is the inner product
`⟪z n i, θ⟫` and `‖θ‖ = (θ'θ)^{1/2}` is the Euclidean norm. The field `observed` records the
standing assumption that every trial is observed at least once, `R_n ≥ 1` (implicit in "the
experiment provides `R_n` repetitions of trial `n`"); it forces `J_n ≥ 1`. The field `trials`
records that the experiment has at least one trial. -/
structure Data (K : ℕ) where
  /-- number of trials `N` -/
  N : ℕ
  /-- the experiment has at least one trial -/
  trials : 0 < N
  /-- number of alternatives `J_n` in the alternative set of trial `n` -/
  J : Fin N → ℕ
  /-- attribute vector `z_in = (v^1(s_n, x_in), …, v^K(s_n, x_in))` -/
  z : (n : Fin N) → Fin (J n) → EuclideanSpace ℝ (Fin K)
  /-- `S_in`: the number of times alternative `i` is chosen in the repetitions of trial `n` -/
  S : (n : Fin N) → Fin (J n) → ℕ
  /-- every trial is repeated at least once: `R_n = ∑_i S_in ≥ 1` -/
  observed : ∀ n, 0 < ∑ i, S n i

namespace Data

variable {K : ℕ} (d : Data K)

/-- Number of repetitions of trial `n`, `R_n = ∑_{j=1}^{J_n} S_jn` (p. 114, PDF p. 10). -/
def R (n : Fin d.N) : ℕ := ∑ i, d.S n i

/-- **Equation (16)** (p. 113, PDF p. 9): the conditional logit selection probability
`P_in(θ) = e^{z_in θ} / ∑_{j=1}^{J_n} e^{z_jn θ}`. The denominator is a nonempty sum of
exponentials, hence positive, whenever `J_n ≥ 1`. -/
noncomputable def P (n : Fin d.N) (i : Fin (d.J n)) (θ : EuclideanSpace ℝ (Fin K)) : ℝ :=
  Real.exp ⟪d.z n i, θ⟫ / ∑ j, Real.exp ⟪d.z n j, θ⟫

/-- The probability-weighted mean attribute vector of trial `n`,
`z̄_n(θ) = ∑_{i=1}^{J_n} z_in P_in(θ)` (p. 115, PDF p. 11, under Equation (20)). -/
noncomputable def zbar (n : Fin d.N) (θ : EuclideanSpace ℝ (Fin K)) :
    EuclideanSpace ℝ (Fin K) :=
  ∑ i, d.P n i θ • d.z n i

/-- The constant of the log-likelihood (p. 115, PDF p. 11, after Equation (18)):
`C = ∑_{n=1}^N [log R_n! − ∑_{j=1}^{J_n} log S_jn!]`. -/
noncomputable def C : ℝ :=
  ∑ n, (Real.log ((d.R n).factorial : ℝ) - ∑ j, Real.log ((d.S n j).factorial : ℝ))

/-- **Equation (18)**, first line (p. 115, PDF p. 11): the log-likelihood
`L(θ) = C − ∑_{n=1}^N ∑_{i=1}^{J_n} S_in log ∑_{j=1}^{J_n} e^{(z_jn − z_in) θ}`.

**Formalization Note.** The inner sum `∑_j e^{(z_jn − z_in)θ}` contains the term `j = i`, equal to
`1`, so the logarithm is taken of a number `≥ 1`; no junk value of `Real.log` occurs. -/
noncomputable def L (θ : EuclideanSpace ℝ (Fin K)) : ℝ :=
  d.C - ∑ n, ∑ i, (d.S n i : ℝ) * Real.log (∑ j, Real.exp ⟪d.z n j - d.z n i, θ⟫)

/-- **Equation (19)** (p. 115, PDF p. 11), right-hand side: the vector
`∑_{n=1}^N ∑_{j=1}^{J_n} (S_jn − R_n P_jn(θ)) z_jn`, which the paper identifies as `∂L/∂θ`. -/
noncomputable def grad (θ : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K) :=
  ∑ n, ∑ j, ((d.S n j : ℝ) - (d.R n : ℝ) * d.P n j θ) • d.z n j

/-- **Equation (20)** (p. 115, PDF p. 11), right-hand side, as a linear map: the symmetric operator
`γ ↦ −∑_{n=1}^N R_n ∑_{j=1}^{J_n} P_jn(θ) ⟨z_jn − z̄_n, γ⟩ (z_jn − z̄_n)`, whose matrix is
`−∑_n R_n ∑_j (z_jn − z̄_n)' P_jn (z_jn − z̄_n)`, the paper's `∂²L/∂θ∂θ'`. -/
noncomputable def hess (θ : EuclideanSpace ℝ (Fin K)) :
    EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K) :=
  -∑ n, (d.R n : ℝ) • ∑ j, d.P n j θ •
      (innerSL ℝ (d.z n j - d.zbar n θ)).smulRight (d.z n j - d.zbar n θ)

end Data

end McFadden1974.MLE


