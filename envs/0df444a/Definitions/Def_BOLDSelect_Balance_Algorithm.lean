-- Prove2me | Definitions.Def_BOLDSelect_Balance_Algorithm
-- name    : BOLDSelect_Balance_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:43.274214+00:00
-- url     : https://prove2.me/theorems/20b531bd-27e1-46f7-9a08-f91ba66586bc
-- title:
--   §2–§3, Figure 1, pp. 3369–3372 — the observation array, sample sizes and means, $u^n_{x,y}$ (10), $\Gamma^n_{x,y}$ (11), the balance sum (12) and the BOLD allocation
-- statement:
--   This file fixes the sampling model and the Balancing Optimal Large Deviations (BOLD) allocation of Chen and Ryzhov.
--
--   **Sampling model.** There are $M$ alternatives. Alternative $x$ produces independent samples from a law $F_x$. On a probability space $(\Omega,\mathcal F,P)$, an **observation array** is a family of real random variables $W_{x,k}$ ($x$ an alternative, $k = 0,1,2,\dots$), where $W_{x,k}$ is the $(k+1)$-th sample taken from $x$: every $W_{x,k}$ is measurable with law $F_x$, and the whole family is mutually independent.
--
--   **Sample sizes and sample means.** Along one realization, let $x^0, x^1, \dots$ be the alternatives chosen at stages $0,1,\dots$. The sample size of $x$ at time $n$ is
--   $$N^n_x = \sum_{m=0}^{n-1} \mathbf 1_{\{x^m = x\}},$$
--   and the sample mean is
--   $$\theta^n_x = \frac1{N^n_x}\sum_{k=0}^{N^n_x - 1} W_{x,k} \quad (N^n_x > 0), \qquad \theta^n_x = \theta^0_x \quad (N^n_x = 0),$$
--   where $\theta^0$ is an arbitrary initial vector. The observation made at stage $m$ is $W^{m+1}_{x^m} = W_{x^m, N^m_{x^m}}$.
--
--   **Plug-in quantities.** At a state with sample sizes $N$ and sample means $\theta$, and for alternatives $x \neq y$:
--   1. $u_{x,y}$ is a solution $u$, lying between $\theta_x$ and $\theta_y$, of equation (10):
--   $$N_x D_x(u;\theta_x) + N_y D_y(u;\theta_y) = 0;$$
--   2. the rescaled approximate rate (11) is
--   $$\Gamma_{x,y} = N_x I_x(u_{x,y};\theta_x) + N_y I_y(u_{x,y};\theta_y);$$
--   3. for a designated alternative $b$, the balance sum (the left side of (12)) is
--   $$\Delta_b = \sum_{x \neq b} \frac{I_b(u_{b,x};\theta_b)}{I_x(u_{b,x};\theta_x)}.$$
--   Here $I_x$ and $D_x$ are the rate function and its derivative from the rate-function definition file.
--
--   **The BOLD allocation (Figure 1).** At time $n$, with state $(N^n,\theta^n)$:
--   1. (Step 1) if $\arg\max_x \theta^n_x$ is not unique, sample $x^{*,n}$, an element of the argmax with the smallest sample size among the argmax (further ties arbitrary);
--   2. (Steps 2–3) if $\arg\max_x \theta^n_x = \{b\}$, then sample $b$ if $\Delta_b > 1$ (condition (12)); otherwise sample an alternative $x \neq b$ minimizing $\Gamma^n_{b,x}$ (13), ties arbitrary.
--
--   An allocation sequence is a **run of BOLD** on a realization of the observation array, from initial means $\theta^0$, if at every stage $n$ its choice $x^n$ is one that these rules allow (Step 0 is $N^0_x = 0$ for all $x$).
--
--   These objects are what Theorems 1–4 of the paper speak about.
--
--   **Formalization Note** The observation array replaces the paper's "observe $W^{n+1}_{x^n} \sim F_{x^n}$" with decisions measurable with respect to the past; the two models give the same law of the sample path (the standard "stack of rewards" construction). BOLD is a predicate on allocation sequences, not a function: every tie-breaking rule the paper allows is admitted. The solution $u_{x,y}$ of (10) is chosen by `Classical.choose` among the solutions between $\theta_x$ and $\theta_y$; the paper asserts this solution is unique, and this is not assumed. When (10) has no solution there (a degenerate state), $u_{x,y} = \theta_x$. Ratios and $\Gamma$ are computed in $[0,\infty]$: $a/0 = \infty$ for $a > 0$ (so a never-sampled leader with $I_x(u) = 0$ triggers (12), as in the paper), $0/0 = 0$, $\infty/\infty = 0$, $0\cdot\infty = 0$. Alternatives are `Fin M`, indexed $0,\dots,M-1$; stages start at $n=0$.
-- source:
--   Chen & Ryzhov, Balancing Optimal Large Deviations in Ranking and Selection, Proc. 2019 Winter Simulation Conference, pp. 3369–3372, §2 (sampling model, N^n_x, θ^n_x, x^{*,n}), §3 (10)–(13), Figure 1

import Mathlib
import Definitions.Def_BOLDSelect_Balance_RateFunction

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BOLDSelect.Balance

/-!
Chen & Ryzhov, *Balancing Optimal Large Deviations in Ranking and Selection*, Proc. 2019 Winter
Simulation Conference, §2 (pp. 3369–3370), §3 ((10)–(13) and Figure 1, pp. 3371–3372).

The sampling model is an observation array: `W x k` is the `(k+1)`-th sample taken from alternative
`x`. Along one sample path `w : Fin M → ℕ → ℝ` and an allocation sequence `xs : ℕ → Fin M` (the
paper's `x^0, x^1, …`), the paper's observation `W^{m+1}_{x^m}` is `w (xs m) (N^m_{xs m})`.
-/

/-- The observation array of §2: every `W x k` is measurable with law `F x` (the sampling
distribution of alternative `x`), and the whole family `{W x k}` is mutually independent. -/
structure ObsArray {M : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Fin M → Measure ℝ) (W : Fin M → ℕ → Ω → ℝ) : Prop where
  meas : ∀ x k, Measurable (W x k)
  law : ∀ x k, P.map (W x k) = F x
  indep : iIndepFun (fun p : Fin M × ℕ => W p.1 p.2) P

/-! ### Sample sizes and sample means along a path (p. 3370) -/

/-- `N^n_x = ∑_{m=0}^{n-1} 1_{x^m = x}`, the number of samples assigned to `x` in stages `0, …, n-1`. -/
def sampleCount {M : ℕ} (xs : ℕ → Fin M) (n : ℕ) (x : Fin M) : ℕ :=
  ((Finset.range n).filter (fun m => xs m = x)).card

/-- The sample mean `θ^n_x = (1/N^n_x) ∑_{k < N^n_x} w x k` of the first `N^n_x` samples of `x`, and
the arbitrary initial value `θ0 x` while `N^n_x = 0` (the paper's "`θ^0_x` chosen arbitrarily"). -/
noncomputable def sampleMean {M : ℕ} (θ0 : Fin M → ℝ) (w : Fin M → ℕ → ℝ) (xs : ℕ → Fin M)
    (n : ℕ) (x : Fin M) : ℝ :=
  if sampleCount xs n x = 0 then θ0 x
  else (∑ k ∈ Finset.range (sampleCount xs n x), w x k) / (sampleCount xs n x : ℝ)

/-! ### The plug-in quantities at a state `(N, θ)` (pp. 3371–3372) -/

open Classical in
/-- `u^n_{x,y}`: a solution `u` of (10), `N_x D_x(u;θ_x) + N_y D_y(u;θ_y) = 0`, lying between `θ_x`
and `θ_y`; the paper asserts the solution is unique. If (10) has no solution there, the value is
`θ_x` (a junk value that only occurs in degenerate states). -/
noncomputable def root {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (N : Fin M → ℕ) (θ : Fin M → ℝ)
    (x y : Fin M) : ℝ :=
  if h : ∃ u ∈ Set.uIcc (θ x) (θ y),
      (N x : ℝ) * rateD Fam x u (θ x) + (N y : ℝ) * rateD Fam y u (θ y) = 0
  then h.choose else θ x

/-- `Γ_{x,y} = N_x I_x(u_{x,y};θ_x) + N_y I_y(u_{x,y};θ_y)` (11), in `[0, ∞]`. -/
noncomputable def gammaRate {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (N : Fin M → ℕ)
    (θ : Fin M → ℝ) (x y : Fin M) : ℝ≥0∞ :=
  (N x : ℝ≥0∞) * rateE Fam x (root Fam N θ x y) (θ x)
    + (N y : ℝ≥0∞) * rateE Fam y (root Fam N θ x y) (θ y)

/-- The left side of (12) (and of Theorem 3) for a designated alternative `b`:
`∑_{x ≠ b} I_b(u_{b,x};θ_b) / I_x(u_{b,x};θ_x)`, computed in `[0, ∞]` (so `a/0 = ∞` for `a > 0`,
`0/0 = 0` and `∞/∞ = 0`). -/
noncomputable def balanceSum {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (N : Fin M → ℕ)
    (θ : Fin M → ℝ) (b : Fin M) : ℝ≥0∞ :=
  ∑ x ∈ Finset.univ.erase b,
    rateE Fam b (root Fam N θ b x) (θ b) / rateE Fam x (root Fam N θ b x) (θ x)

/-- `argmax_x θ_x`, as a finite set. -/
noncomputable def argmaxSet {M : ℕ} (θ : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun y => ∀ z, θ z ≤ θ y)

/-! ### The BOLD algorithm (Figure 1, p. 3372) -/

/-- `c` is a choice that Figure 1 allows at the state with sample sizes `N` and sample means `θ`:
* Step 1: if `argmax θ` is not a singleton, `c` is `x^{*,n}`, i.e. an element of `argmax θ` with the
  smallest sample size among `argmax θ` (further ties arbitrary);
* Steps 2–3: if `argmax θ = {b}`, then `c = b` when (12) holds, and otherwise `c` is an argmin of
  `Γ_{b,x}` over `x ≠ b` (13), ties arbitrary. -/
def BOLDChoice {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (N : Fin M → ℕ) (θ : Fin M → ℝ)
    (c : Fin M) : Prop :=
  ((argmaxSet θ).card ≠ 1 → c ∈ argmaxSet θ ∧ ∀ y ∈ argmaxSet θ, N c ≤ N y) ∧
  (∀ b, argmaxSet θ = {b} →
    (1 < balanceSum Fam N θ b → c = b) ∧
    (¬ 1 < balanceSum Fam N θ b →
      c ≠ b ∧ ∀ x, x ≠ b → gammaRate Fam N θ b c ≤ gammaRate Fam N θ b x))

/-- The allocation `xs` is a run of BOLD on the observation path `w` started from the initial
means `θ0` (Step 0: `N^0 = 0`): at every stage `n`, `xs n` is a choice allowed by Figure 1 at the
time-`n` state `(N^n, θ^n)`. -/
def IsBOLD {M : ℕ} (Fam : Fin M → ℝ → Measure ℝ) (θ0 : Fin M → ℝ) (w : Fin M → ℕ → ℝ)
    (xs : ℕ → Fin M) : Prop :=
  ∀ n, BOLDChoice Fam (sampleCount xs n) (sampleMean θ0 w xs n) (xs n)

end BOLDSelect.Balance


