-- Prove2me | Definitions.Def_SumReLU_reluSum
-- name    : SumReLU_reluSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:23.203423+00:00
-- url     : https://prove2.me/theorems/d38de759-7754-4bab-a1bd-914a5714a3b9
-- title:
--   Positive linear combinations of ReLUs and the class $\mathcal C_{d,k}$
-- statement:
--   Let $\sigma(t)=\max\{0,t\}$ be the ReLU activation. For $d,k\in\mathbb Z_+$, coefficients $\beta_1,\dots,\beta_k\in\mathbb R$ and hidden weight vectors $w_1,\dots,w_k\in\mathbb R^d$, put
--   $$
--   f(x)=\sum_{i=1}^k\beta_i\,\sigma(w_i\cdot x)\qquad(x\in\mathbb R^d).
--   $$
--   The class $\mathcal C_{d,k}$ consists of the functions of this form with $\beta_i\in[0,1]$ and $\|w_i\|_2=1$ for all $i\in[k]$. A distribution of $(x,f(x))$ with $x\sim N(0,I_d)$ and $f\in\mathcal C_{d,k}$ is called a Gaussian sum of $k$ ReLUs.
--
--   This is the concept class of the paper; every statement of the mission is about a target $f\in\mathcal C_{d,k}$, given by its parameters $(\beta,w)$.
--
--   **Formalization Note** Indices are `Fin k` and $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. `reluSum β w` is $f$ and `InClass β w` is the membership condition; $d,k\ge1$ are hypotheses of the theorems.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Definition 1.1, p.1 (PDF p.3); Terminology, p.2 (PDF p.4)

import Mathlib

namespace SumReLU

/-- The ReLU activation `σ(t) = max{0, t}`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Definition 1.1, p.1 (PDF p.3). -/
noncomputable def relu (t : ℝ) : ℝ := max 0 t

/-- A positive linear combination of ReLUs, `f(x) = ∑_{i ∈ [k]} β_i σ(w_i · x)` on `ℝᵈ`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Definition 1.1, p.1 (PDF p.3): "let C_{d,k} denote the class of functions f : ℝᵈ → ℝ of the
form f(x) = ∑_{i=1}^k β_i σ(w_i · x), where β_i ∈ [0, 1] and ‖w_i‖₂ = 1 for all i ∈ [k]."

**Formalization Note.** The indices are `Fin k` (0-based for the paper's `[k]`); `ℝᵈ` is
`EuclideanSpace ℝ (Fin d)` with its standard inner product. No constraint on `β`, `w` is built
in; membership in `C_{d,k}` is `InClass`. -/
noncomputable def reluSum {d k : ℕ} (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, β i * relu (inner ℝ (w i) x)

/-- **The class `C_{d,k}`** (Definition 1.1, p.1, PDF p.3): the coefficients lie in `[0, 1]` and the
hidden weight vectors are unit vectors. A function `f` belongs to `C_{d,k}` iff
`f = reluSum β w` for some `β`, `w` with `InClass β w`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Definition 1.1, p.1 (PDF p.3); the same conditions define a "Gaussian sum of k ReLUs"
(Terminology, p.2, PDF p.4).

**Formalization Note.** `d, k ∈ ℤ₊` are hypotheses of the theorems that use this predicate. -/
def InClass {d k : ℕ} (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ i, β i ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ i, ‖w i‖ = 1

end SumReLU


