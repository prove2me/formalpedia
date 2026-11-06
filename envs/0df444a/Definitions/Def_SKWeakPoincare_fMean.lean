-- Prove2me | Definitions.Def_SKWeakPoincare_fMean
-- name    : SKWeakPoincare_fMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:03.483205+00:00
-- url     : https://prove2.me/theorems/8ea22e04-ab53-4238-8cde-44bf6dd4dec8
-- title:
--   Finite-space Markov chain notions: mean, variance, oscillation, total variation, Dirichlet form, reversibility, warmness, multi-stage runs
-- statement:
--   Let $\alpha$ be a finite set. A **law** on $\alpha$ is a function $\mu:\alpha\to\mathbb R$ with $\mu(x)\ge0$ and $\sum_x\mu(x)=1$, and a **Markov kernel** is a matrix $P$ with $P(x,y)\ge0$ and $\sum_yP(x,y)=1$ for every $x$. For $f:\alpha\to\mathbb R$ this module defines
--
--   1. the mean $E_\mu[f]=\sum_x\mu(x)f(x)$ and the variance $\mathrm{Var}_\mu[f]=E_\mu[(f-E_\mu f)^2]$;
--   2. the oscillation $\mathrm{osc}(f)=\max f-\min f$ (for nonempty $\alpha$);
--   3. the total variation distance $d_{\mathrm{TV}}(\mu,\nu)=\tfrac12\sum_x|\mu(x)-\nu(x)|$;
--   4. the Dirichlet form $\mathcal E_\mu(f,f)=\langle f,(I-P)f\rangle_\mu=\sum_x\mu(x)f(x)\big(f(x)-(Pf)(x)\big)$;
--   5. reversibility (detailed balance) $\mu(x)P(x,y)=\mu(y)P(y,x)$;
--   6. nonnegative spectrum: $\langle f,Pf\rangle_\mu\ge0$ for all $f$;
--   7. warmness: $\mu_{\mathrm{init}}$ is $B$-warm for $\mu$ if $\mu_{\mathrm{init}}(x)\le B\mu(x)$ for all $x$;
--   8. the law $\mu_0P_1^{k_1}\cdots P_j^{k_j}$ after $j$ stages of a multi-stage chain.
--
--   These are the objects of the warm-start and simulated-annealing bounds (Lemmas 6.6 and 6.7).
--
--   **Formalization Note** Laws are real functions and kernels real matrices; $\mu P$ is the row-vector product `Matrix.vecMul`. For a reversible Markov kernel, $\langle f,Pf\rangle_\mu\le\langle f,f\rangle_\mu$ holds automatically, so nonnegative spectrum is the same as spectrum in $[0,1]$. On a finite space, $\mu_{\mathrm{init}}(S)\le B\mu(S)$ for every set $S$ is equivalent to the pointwise bound.
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Section 6, p.37 (⟨f,g⟩_μ, E_μ(f,f) = ⟨f,(I−P)f⟩_μ, osc), p.42 (B-warm laws, Lemma 6.6), p.43 (Lemma 6.7)

import Mathlib

namespace SKWeakPoincare

/-! # Finite-space Markov chain notions (Hou–Liu–Yu, Section 6, pp. 37, 42–43)

Hou–Liu–Yu, *Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy
for the Sherrington–Kirkpatrick model*, arXiv:2610.09882, Section 6, p. 37 (`⟨f, g⟩_μ`,
`𝓔_μ(f, f) = ⟨f, (I − P)f⟩_μ`, `osc(f) = sup f − inf f`), p. 42 (warm laws, Lemma 6.6) and
p. 43 (Lemma 6.7).

**Formalization Note.** A law on a finite type `α` is a function `μ : α → ℝ`, a Markov kernel is a
matrix `P : Matrix α α ℝ` (row `x` is the law of the next state from `x`), and `μ P` is the row-vector
product `Matrix.vecMul μ P`. -/

/-- Expectation `E_μ[f] = Σ_x μ(x) f(x)` under a law `μ` on a finite type. -/
noncomputable def fMean {α : Type*} [Fintype α] (μ : α → ℝ) (f : α → ℝ) : ℝ :=
  ∑ x, μ x * f x

/-- Variance `Var_μ[f] = E_μ[(f − E_μ f)^2]`. -/
noncomputable def fVar {α : Type*} [Fintype α] (μ : α → ℝ) (f : α → ℝ) : ℝ :=
  fMean μ (fun x => (f x - fMean μ f) ^ 2)

/-- Oscillation `osc(f) = max f − min f` of a function on a finite nonempty type. -/
noncomputable def fOsc {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f - Finset.univ.inf' Finset.univ_nonempty f

/-- Total variation distance `d_TV(μ, ν) = ½ Σ_x |μ(x) − ν(x)|`. -/
noncomputable def fTV {α : Type*} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |μ x - ν x|

/-- Dirichlet form `𝓔_μ(f, f) = ⟨f, (I − P) f⟩_μ = Σ_x μ(x) f(x) (f(x) − (Pf)(x))` (p. 37). -/
noncomputable def fDirichlet {α : Type*} [Fintype α] (μ : α → ℝ) (P : Matrix α α ℝ)
    (f : α → ℝ) : ℝ :=
  ∑ x, μ x * f x * (f x - ∑ y, P x y * f y)

/-- `μ` is a probability law: nonnegative weights summing to one. -/
def IsLaw {α : Type*} [Fintype α] (μ : α → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- `P` is a Markov kernel (stochastic matrix): nonnegative entries, rows summing to one. -/
def IsStochastic {α : Type*} [Fintype α] (P : Matrix α α ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧ ∀ x, ∑ y, P x y = 1

/-- Detailed balance `μ(x) P(x, y) = μ(y) P(y, x)`: `P` is reversible with respect to `μ`
(for a stochastic `P` this makes `μ` stationary). -/
def IsReversible {α : Type*} [Fintype α] (μ : α → ℝ) (P : Matrix α α ℝ) : Prop :=
  ∀ x y, μ x * P x y = μ y * P y x

/-- `P` has nonnegative spectrum in `L²(μ)`: `⟨f, P f⟩_μ ≥ 0` for every `f`.

**Formalization Note.** For a stochastic `P` reversible with respect to a law `μ`, `P` is
self-adjoint on `L²(μ)` and `⟨f, Pf⟩_μ ≤ ⟨f, f⟩_μ` always holds, so this predicate is also the
paper's "spectrum in `[0, 1]`" (Lemma 6.6). It is stated as a quadratic form because `P` is
self-adjoint in `L²(μ)`, not symmetric as a matrix. -/
def HasNonnegSpectrum {α : Type*} [Fintype α] (μ : α → ℝ) (P : Matrix α α ℝ) : Prop :=
  ∀ f : α → ℝ, 0 ≤ ∑ x, μ x * f x * ∑ y, P x y * f y

/-- `μinit` is `B`-warm with respect to `μ`: `μinit(x) ≤ B μ(x)` for every `x`.

**Formalization Note.** The paper (p. 42) says `μinit(S) ≤ B μ(S)` for every measurable `S`; on a
finite space this is equivalent to the pointwise bound. Lemma 6.7's `μ_{j−1} ≤ B_j μ_j` is the same
condition. -/
def IsWarm {α : Type*} [Fintype α] (μinit μ : α → ℝ) (B : ℝ) : Prop :=
  ∀ x, μinit x ≤ B * μ x

/-- The law `μ₀ P₁^{k₁} ⋯ P_j^{k_j}` after the first `j` stages of a multi-stage chain
(`chainRun μ₀ P k 0 = μ₀`). -/
noncomputable def chainRun {α : Type*} [Fintype α] [DecidableEq α] (μ₀ : α → ℝ) (P : ℕ → Matrix α α ℝ)
    (k : ℕ → ℕ) : ℕ → α → ℝ
  | 0 => μ₀
  | j + 1 => Matrix.vecMul (chainRun μ₀ P k j) (P (j + 1) ^ k (j + 1))

end SKWeakPoincare


