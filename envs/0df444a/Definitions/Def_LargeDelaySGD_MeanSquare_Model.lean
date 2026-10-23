-- Prove2me | Definitions.Def_LargeDelaySGD_MeanSquare_Model
-- name    : LargeDelaySGD_MeanSquare_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:51.300472+00:00
-- url     : https://prove2.me/theorems/f5463bfa-86cc-483a-b0f7-6439cc42977d
-- title:
--   §2–§3, pp. 4–10 — (Opt), f = E[F] (1), ∇F, Assumption 1, Algorithm 3 (DASGD with delays s(n)), Assumption 2 (four delay/step-size regimes)
-- statement:
--   This definition file sets up the model of Zhou, Mertikopoulos, Bambos, Glynn and Ye for unconstrained stochastic optimization with delayed gradients.
--
--   **Problem.** Let $(\Xi,\mu)$ be a probability space and $F:\mathbb R^d\times\Xi\to\mathbb R$ a random function. The objective is
--
--   $$f(x)=\mathbb E[F(x;\xi)]=\int_\Xi F(x;\xi)\,d\mu(\xi),\qquad x\in\mathbb R^d,$$
--
--   and $\nabla F(x;\xi)$ denotes the gradient of $F(\cdot;\xi)$ in $x$ only.
--
--   **Assumption 1** (with named constants $B$ and $L$): $F(x;\cdot)$ is $\mu$-integrable for every $x$; for $\mu$-almost every $\xi$, $F(\cdot;\xi)$ is differentiable; $\nabla F(x;\cdot)$ is square integrable with $\mathbb E\|\nabla F(x;\xi)\|_2^2\le B$ for all $x$ (finite second moment); and $x\mapsto\mathbb E[\nabla F(x;\xi)]$ is $L$-Lipschitz (Lipschitz in the mean).
--
--   **Delays.** A delay schedule is a sequence $s:\mathbb N\to\mathbb N$ with $s(n)\le n$: the gradient applied at step $n$ was computed at the iterate $X_{s(n)}$, so its delay is $n-s(n)$. The delay term used in the analysis is
--
--   $$\alpha_{n+1}\sum_{r=s(n)}^{n-1}\alpha_{r+1}.$$
--
--   **Assumption 2.** The step sizes are positive, $s(n)\le n$, and one of the following holds:
--   1. *Bounded delays:* $n-s(n)\le D$ for some $D$, $\sum_n\alpha_n^2<\infty$ and $\sum_n\alpha_n=\infty$;
--   2. *Sublinear delays:* $n-s(n)\le K(s(n)+1)^p$ for some $0<p<1$ and $K$, and $\alpha_n=c/n$ for all large $n$, some $c>0$;
--   3. *Linear delays:* $n-s(n)\le K(s(n)+1)$ for some $K$, and $\alpha_n=c/(n\log n)$ for all large $n$, some $c>0$;
--   4. *Polynomial delays:* $n-s(n)\le K(s(n)+1)^q$ for some $q\ge1$ and $K$, and $\alpha_n=c/(n\log n\log\log n)$ for all large $n$, some $c>0$.
--
--   **Noise and iterates.** The noise sequence $(\omega_n)_{n\ge0}$ on a probability space $(\Omega,\mathbb P)$ is i.i.d. with law $\mu$. The DASGD iterates (Algorithm 3) are
--
--   $$X_0=x_0,\qquad X_{n+1}=X_n-\alpha_{n+1}\nabla F(X_{s(n)},\omega_{n+1}).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and $\nabla F$ is Mathlib's `gradient`, which returns $0$ where $F(\cdot;\xi)$ is not differentiable (a $\mu$-null set of $\xi$ under Assumption 1). The paper writes one symbol $\omega$ for both the argument of $F$ and the noise sequence; here they live on two named spaces $(\Xi,\mu)$ and $(\Omega,\mathbb P)$. Two hypotheses implicit in the paper are made explicit: integrability of $F(x;\cdot)$ (so that (1) exists) and joint measurability of $(x,\xi)\mapsto\nabla F(x;\xi)$ (so that the iterates are random variables; footnote 1 only asks measurability in $\xi$ for each $x$). "$\sup_x\mathbb E\|\nabla F\|^2<\infty$" is encoded as a parameter $B$ bounding every second moment together with square integrability, and "Lipschitz" as a parameter $L$. The schedule $s$ is deterministic. "$d_n=O(n^q)$" is stated on received gradients, $n-s(n)\le K(s(n)+1)^q$; the "$+1$" covers $s(n)=0$. "$\alpha_n\propto\varphi(n)$" means $\alpha_n=c\,\varphi(n)$ from some index $N$ on, because $1/(n\log n)$ and $1/(n\log n\log\log n)$ are undefined or nonpositive for small $n$; together with positivity of every $\alpha_n$ this rules out the junk values of `Real.log`. In regime 1, $\sum\alpha_n^2<\infty$ and $\sum\alpha_n=\infty$ are stated over $n\ge0$, which is equivalent to the paper's $n\ge1$.
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1, pp. 4–10, (Opt), (1), footnotes 1–2, Assumption 1, Algorithm 3, s(n) and d_n (p. 9), Assumption 2

import Mathlib

namespace LargeDelaySGD.MeanSquare

open MeasureTheory ProbabilityTheory

variable {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

/-- `∇F(x; ξ)`: the gradient of `F(·; ξ)` in `x` (footnote 2, p. 5). It is the junk value `0` at
points where `F(·; ξ)` is not differentiable; Assumption 1 (1) makes that a `μ`-null set of `ξ`. -/
noncomputable def stochGrad (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (ξ : Ξ) : EuclideanSpace ℝ (Fin d) :=
  gradient (fun y => F y ξ) x

/-- The objective `f(x) = E[F(x; ω)] = ∫ F(x; ω) dP(ω)`, equation (1), p. 5. -/
noncomputable def objective (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (μ : Measure Ξ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ ξ, F x ξ ∂μ

/-- Assumption 1 (p. 5) on `X = ℝ^d`, with `B` a bound for `sup_x E‖∇F(x; ω)‖²₂` and `L` a
Lipschitz constant of `x ↦ E[∇F(x; ω)]`. The fields `integrable` (the expectation in (1) exists)
and `measurable_grad` (joint measurability of `∇F`, so that the iterates are random variables)
are the disclosed implicit hypotheses. -/
structure Assumption1 (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (μ : Measure Ξ) (B : ℝ)
    (L : NNReal) : Prop where
  integrable : ∀ x, Integrable (F x) μ
  measurable_grad : Measurable (Function.uncurry (stochGrad F))
  differentiable : ∀ᵐ ξ ∂μ, Differentiable ℝ (fun x => F x ξ)
  memLp : ∀ x, MemLp (stochGrad F x) 2 μ
  second_moment : ∀ x, ∫ ξ, ‖stochGrad F x ξ‖ ^ 2 ∂μ ≤ B
  lipschitz : LipschitzWith L (fun x => ∫ ξ, stochGrad F x ξ ∂μ)

/-- The delay term `α_{n+1} Σ_{r=s(n)}^{n−1} α_{r+1}` of (B.6)–(B.10), p. 24–26. -/
noncomputable def delaySum (α : ℕ → ℝ) (s : ℕ → ℕ) (n : ℕ) : ℝ :=
  α (n + 1) * ∑ r ∈ Finset.Ico (s n) n, α (r + 1)

/-- Assumption 2 (1), p. 9: bounded delays `n − s(n) ≤ D`, `Σ α_n² < ∞`, `Σ α_n = ∞`. -/
def BoundedRegime (α : ℕ → ℝ) (s : ℕ → ℕ) : Prop :=
  (∃ D : ℕ, ∀ n, n ≤ s n + D) ∧ Summable (fun n => α n ^ 2) ∧ ¬ Summable α

/-- Assumption 2 (2), p. 9: `d = O(n^p)` for some `0 < p < 1`, and `α_n ∝ 1/n` (from some `N` on). -/
def SublinearRegime (α : ℕ → ℝ) (s : ℕ → ℕ) : Prop :=
  ∃ p : ℝ, 0 < p ∧ p < 1 ∧ (∃ K : ℝ, ∀ n : ℕ, (n : ℝ) ≤ s n + K * ((s n : ℝ) + 1) ^ p) ∧
    ∃ c > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, α n = c / n

/-- Assumption 2 (3), p. 10: `d = O(n)` and `α_n ∝ 1/(n log n)` (from some `N` on). -/
def LinearRegime (α : ℕ → ℝ) (s : ℕ → ℕ) : Prop :=
  (∃ K : ℝ, ∀ n : ℕ, (n : ℝ) ≤ s n + K * ((s n : ℝ) + 1)) ∧
    ∃ c > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, α n = c / (n * Real.log n)

/-- Assumption 2 (4), p. 10: `d = O(n^q)` for some `q ≥ 1`, and `α_n ∝ 1/(n log n log log n)`
(from some `N` on). -/
def PolynomialRegime (α : ℕ → ℝ) (s : ℕ → ℕ) : Prop :=
  ∃ q : ℝ, 1 ≤ q ∧ (∃ K : ℝ, ∀ n : ℕ, (n : ℝ) ≤ s n + K * ((s n : ℝ) + 1) ^ q) ∧
    ∃ c > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, α n = c / (n * Real.log n * Real.log (Real.log n))

/-- Assumption 2, pp. 9–10: positive step sizes, `s(n) ≤ n`, and one of the four regimes. -/
def Assumption2 (α : ℕ → ℝ) (s : ℕ → ℕ) : Prop :=
  (∀ n, 0 < α n) ∧ (∀ n, s n ≤ n) ∧
    (BoundedRegime α s ∨ SublinearRegime α s ∨ LinearRegime α s ∨ PolynomialRegime α s)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The noise sequence `ω_n` is i.i.d. with law `μ` (p. 9: "ωn's are iid"). -/
structure IIDNoise (P : Measure Ω) (μ : Measure Ξ) (ω : ℕ → Ω → Ξ) : Prop where
  measurable : ∀ n, Measurable (ω n)
  indep : iIndepFun ω P
  law : ∀ n, P.map (ω n) = μ

/-- Algorithm 3 (DASGD), p. 8: `X_0 = x₀` and `X_{n+1} = X_n − α_{n+1} ∇F(X_{s(n)}, ω_{n+1})`. -/
def IsDASGD (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (α : ℕ → ℝ) (s : ℕ → ℕ)
    (ω : ℕ → Ω → Ξ) (x₀ : EuclideanSpace ℝ (Fin d)) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  (∀ a, X 0 a = x₀) ∧
    ∀ n a, X (n + 1) a = X n a - α (n + 1) • stochGrad F (X (s n) a) (ω (n + 1) a)

end LargeDelaySGD.MeanSquare


