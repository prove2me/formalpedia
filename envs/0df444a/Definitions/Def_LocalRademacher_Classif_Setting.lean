-- Prove2me | Definitions.Def_LocalRademacher_Classif_Setting
-- name    : LocalRademacher_Classif_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:26:42.086065+00:00
-- url     : https://prove2.me/theorems/9c527bba-594e-4967-b1f5-7403c9beceed
-- title:
--   §6.2, pp. 28–29 — the discrete loss ℓ, empirical losses Pₙℓ, the loss class {ℓ_f : Pₙℓ_f ≤ b}, J(μ) and ψ̂ₙ(r)
-- statement:
--   Let $\mathcal X$ be an input space, $X_1,\dots,X_n\in\mathcal X$ fixed inputs and $Y_1,\dots,Y_n\in\{-1,1\}$ fixed labels. A classifier is a function $f:\mathcal X\to\mathbb R$; the class $\mathcal F$ of interest consists of classifiers with values in $\{-1,1\}$. Sign vectors $\sigma=(\sigma_1,\dots,\sigma_n)\in\{-1,1\}^n$ are indexed by $\{\text{true},\text{false}\}^n$, with $\text{true}\mapsto 1$.
--
--   1. The **discrete loss** is $\ell(y,y')=\mathbf 1[y\neq y']$, that is $0$ if $y=y'$ and $1$ otherwise.
--   2. For a vector $z\in\mathbb R^n$ (the labels $Y$, or a sign vector $\sigma$) the **empirical loss** of $f$ is
--   $$P_n\ell(f(X),z)=\frac1n\sum_{i=1}^n \ell(f(X_i),z_i).$$
--   With $z=Y$ this is $P_n\ell_f$, the empirical risk of $f$.
--   3. For $b\in\mathbb R$, the set of **loss vectors** $\{(\ell(f(X_1),Y_1),\dots,\ell(f(X_n),Y_n)) : f\in\mathcal F,\ P_n\ell_f\le b\}\subseteq\mathbb R^n$. Its empirical Rademacher average
--   $$\mathbb E_\sigma R_n\{\ell_f : f\in\mathcal F,\ P_n\ell_f\le b\}=\frac1n\,\mathbb E_\sigma\sup_{f\in\mathcal F,\ P_n\ell_f\le b}\sum_{i=1}^n\sigma_i\,\ell(f(X_i),Y_i)$$
--   is the published Rademacher complexity `UnderstandingML.rademacher` of this set, the expectation $\mathbb E_\sigma$ being the average over the $2^n$ sign vectors.
--   4. For a sign vector $\sigma$ and $\mu\ge0$, the **weighted empirical risk minimum**
--   $$J(\mu)=\min_{f\in\mathcal F}\frac1n\sum_{i=1}^n|\sigma_i+\mu Y_i|\,\ell\big(f(X_i),\operatorname{sign}(\sigma_i+\mu Y_i)\big).$$
--   5. For $c,x,r\in\mathbb R$, the **empirical local Rademacher complexity of the classification loss class**
--   $$\hat\psi_n(r)=c\sup_{\alpha\in[\sqrt{2r},1]}\alpha\,\mathbb E_\sigma R_n\{\ell_f : f\in\mathcal F,\ P_n\ell_f\le 2r/\alpha^2\}+\frac{26x}{n}.$$
--   Corollary 6.2 takes $c=20$; Theorem 6.3 writes a generic multiplier $c$.
--
--   These are the objects of Theorem 6.3: $\hat\psi_n$ is the complexity whose fixed point controls the error of empirical risk minimization in Corollary 6.2, and $J(\mu)$ is the value of a weighted classification problem with noisy labels, which can be computed by any weighted empirical risk minimizer.
--
--   **Formalization Note** The loss $\ell$ is defined on all real pairs, not only on $\{\pm1\}$, because $J(\mu)$ evaluates it at $\operatorname{sign}(\sigma_i+\mu Y_i)$, which is $0$ when $\sigma_i+\mu Y_i=0$; Lean's `Real.sign 0 = 0`, and such a term carries the weight $|\sigma_i+\mu Y_i|=0$, so the convention does not change $J$. The minimum in $J$ and the supremum in $\hat\psi_n$ are Lean's real infimum and supremum over a subtype; they are the true minimum and supremum when $\mathcal F$ is nonempty and $0<r\le 1/2$, which every theorem using them assumes (an empty index set would give the junk value $0$). Labels and sign vectors are real vectors so that the same empirical loss serves for both.
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, §1 notation p. 3; §6.2 p. 28 (discrete loss; Corollary 6.2, definition of ψ̂ₙ); Theorem 6.3, pp. 28–29 (J(μ)); Lemma 6.4, p. 29 (Pₙℓ(f(X),σ))

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher

namespace LocalRademacher.Classif

/-- The **discrete loss** `ℓ(y, y') = 1[y ≠ y']` of §6.2 (Bartlett, Bousquet & Mendelson,
arXiv:math/0508275v1, p. 28). It is defined on all of `ℝ` rather than on `{±1}` because the
quantity `J(μ)` of Theorem 6.3 evaluates it at `sign(σᵢ + μYᵢ)`, which can be `0`. -/
noncomputable def ell (y y' : ℝ) : ℝ := if y = y' then 0 else 1

/-- The empirical loss `(1/n) ∑ᵢ ℓ(f(Xᵢ), zᵢ)` of the classifier `f` against the label vector `z` on
the inputs `xs = (X₁, …, Xₙ)`. With `z = Y` this is `Pₙℓ_f = Pₙℓ(f(X), Y)`; with `z = σ` (a sign
vector) it is `Pₙℓ(f(X), σ)` (pp. 3, 5, 29). -/
noncomputable def empLoss {X : Type*} {n : ℕ} (xs : Fin n → X) (z : Fin n → ℝ) (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, ell (f (xs i)) (z i)

/-- The evaluation vectors `(ℓ(f(X₁), Y₁), …, ℓ(f(Xₙ), Yₙ))` of the loss functions `ℓ_f` of the
classifiers `f ∈ F` with `Pₙℓ_f ≤ b`. The empirical Rademacher average
`E_σ Rₙ{ℓ_f : f ∈ F, Pₙℓ_f ≤ b}` of p. 28 is `UnderstandingML.rademacher (lossVecs F xs ys b)`. -/
def lossVecs {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (xs : Fin n → X) (ys : Fin n → ℝ) (b : ℝ) :
    Set (Fin n → ℝ) :=
  {v | ∃ f ∈ F, empLoss xs ys f ≤ b ∧ v = fun i => ell (f (xs i)) (ys i)}

/-- The weighted empirical risk minimum of Theorem 6.3 (p. 29), for a fixed sign vector `σ` and
`μ ≥ 0`:
`J(μ) = min_{f ∈ F} (1/n) ∑ᵢ |σᵢ + μYᵢ| ℓ(f(Xᵢ), sign(σᵢ + μYᵢ))`.
The infimum is the real infimum over the subtype `F`; the theorems that use `J` assume `F`
nonempty, and the summands take finitely many values, so it is attained. `Real.sign 0 = 0`
where the page's `sign` is undefined; such a term has weight `|σᵢ + μYᵢ| = 0`, so the convention
does not affect the value. -/
noncomputable def J {X : Type*} {n : ℕ} (F : Set (X → ℝ)) (xs : Fin n → X) (ys : Fin n → ℝ)
    (σ : Fin n → Bool) (μ : ℝ) : ℝ :=
  ⨅ f : F, (1 / (n : ℝ)) * ∑ i, |UnderstandingML.signVec σ i + μ * ys i| *
    ell ((f : X → ℝ) (xs i)) (Real.sign (UnderstandingML.signVec σ i + μ * ys i))

/-- The empirical local Rademacher complexity of the classification loss class
(Corollary 6.2, p. 28, with the generic multiplier `c` of Theorem 6.3 in place of `20`):
`ψ̂ₙ(r) = c sup_{α ∈ [√(2r), 1]} α E_σ Rₙ{ℓ_f : f ∈ F, Pₙℓ_f ≤ 2r/α²} + 26x/n`.
The supremum is the real supremum over the subtype `[√(2r), 1]`; it is a true supremum when
`0 < r ≤ 1/2` (nonempty range, bounded values), which the theorems assume. -/
noncomputable def psiHat {X : Type*} {n : ℕ} (c x r : ℝ) (F : Set (X → ℝ)) (xs : Fin n → X)
    (ys : Fin n → ℝ) : ℝ :=
  c * (⨆ α : Set.Icc (Real.sqrt (2 * r)) 1,
      (α : ℝ) * UnderstandingML.rademacher (lossVecs F xs ys (2 * r / (α : ℝ) ^ 2)))
    + 26 * x / n

end LocalRademacher.Classif


