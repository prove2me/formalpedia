-- Prove2me | Definitions.Def_PorteusSS_Functions
-- name    : PorteusSS_Functions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:51:53.313674+00:00
-- url     : https://prove2.me/theorems/d2fc30c7-fc0f-4a85-8719-9ade2ec599e5
-- title:
--   Function classes of Porteus (1971): Pólya densities, PF-integrability, $C_a(K)$, $C(K)$, quasi-$K$-convexity, generalized $(s,S)$ policies
-- statement:
--   This file fixes the vocabulary of Porteus's analysis of generalized $(s,S)$ policies. All functions are real valued functions of one real variable.
--
--   1. **Convolution** (§X). For $f, g : \mathbb R \to \mathbb R$,
--   $$ (f * g)(y) = \int_{-\infty}^{\infty} f(y - x)\, g(x)\, dx . $$
--   2. **Piecewise continuity** (§X). $f$ is piecewise continuous on an interval $I$ if there is a finite set $A \subseteq I$ such that $f$ is continuous on $I \setminus A$ and, at every point of $A$, the one-sided limits of $f$ exist (as real numbers) whenever they are defined.
--   3. **Pólya frequency functions** (Definitions 5–8). $\varphi$ is $PF_n$ if (a) $0 < \int_{-\infty}^{\infty} \varphi(x)\,dx < \infty$ and (b) for every $1 \le k \le n$, all $x_1 < \dots < x_k$ and all $t_1 < \dots < t_k$,
--   $$ \det\big[\varphi(x_i - t_j)\big]_{i,j=1}^{k} \ge 0 . $$
--   $\varphi$ is a Pólya frequency function ($PFF$) if it is $PF_n$ for every $n \ge 1$; a $PFF$ with $\int \varphi = 1$ is a Pólya density; a Pólya density that vanishes on $R^- = (-\infty, 0)$ is a *one-sided Pólya density*.
--   4. **PF-integrability** (§III). $f$ is PF-integrable if the convolution $f * \psi$ exists (is finite) at every point for every Pólya frequency function $\psi$.
--   5. **Non-$K$-decreasing** (Definition 1). $f$ is non-$K$-decreasing on $X$ if $f(x) \le f(y) + K$ whenever $x, y \in X$ and $x \le y$.
--   6. **The class $C_a(K)$** (Definition 2), for $K \ge 0$ and $a \in \mathbb R$: the functions $f$ which, for some $I \in \{(-\infty, a), (-\infty, a]\}$, are (i) piecewise continuous, (ii) PF-integrable, (iii) nonincreasing on $I$, (iv) non-$K$-decreasing on $\mathbb R \setminus I$, and (v) satisfy $f(x) \to \infty$ as $|x| \to \infty$.
--   7. **The class $C(K)$** (Definition 3), for $K \ge 0$: the continuous functions lying in $C_a(K)$ for some $a \in \mathbb R$.
--   8. **Quasi-$K$-convexity** (Definition 10). $f$ is quasi-$K$-convex on a convex set $X$ if for $x, y \in X$ with $x \le y$ and $0 \le \lambda \le 1$,
--   $$ f(\lambda x + (1-\lambda) y) \le \max\big(f(x),\, f(y) + K\big). $$
--   9. **Generalized $(s,S)$ policy** (Definition 4). An ordering policy function $y$, giving the inventory level after ordering as a function of the level $x$ before ordering, is a generalized $(s,S)$ policy if (i) $y(x) = x$ for $s \le x$ and (ii) $y(z) \ge y(x) \ge S \ge s$ for $z < x < s$.
--   10. **Exponential density** with parameter $\lambda > 0$: $\varphi(t) = \lambda e^{-\lambda t}$ for $t \ge 0$ and $0$ otherwise.
--
--   These classes carry the whole argument: $C(K)$ functions have the $(s,S)$ shape (Lemma 1), and the class is closed under convolution with one-sided Pólya densities (Theorem 1).
--
--   **Formalization Note.** The convolution is a Lebesgue integral over $\mathbb R$, which Lean evaluates to $0$ when the integrand is not integrable; every statement using it either assumes or concludes integrability (PF-integrability is exactly this). Condition (a) of Definition 5 is written as Lebesgue integrability plus a positive integral, which is equivalent because (b) with $k = 1$ forces $\varphi \ge 0$. The requirement $K \ge 0$ of Definitions 2 and 3 is part of the class, so $f \in C_a(K)$ implies $K \ge 0$. Condition (v) is convergence to $+\infty$ along the cocompact filter of $\mathbb R$, i.e. as $x \to \pm\infty$. The parameter of the quasi-$K$-convexity inequality is named $l$ in Lean.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 414, Definitions 1–3; p. 415, Definition 4; p. 421, Definitions 5–8; p. 423, Definition 10 and PF-integrability; pp. 425–426, §X (convolution, piecewise continuity)

import Mathlib

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Convolution shorthand of §X: `conv f g y = ∫_{-∞}^{∞} f (y - x) g(x) dx` (Lebesgue integral
over `ℝ`; it is `0` when the integrand is not integrable, so every use below either assumes or
concludes integrability). -/
noncomputable def conv (f g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x, f (y - x) * g x

/-- Piecewise continuity on an interval `I` (§X): there is a finite set `A ⊆ I` such that
(i) `f` is continuous on `I \ A`, and (ii) at every point of `A` the one-sided limits of `f`
(within `I`) exist as real numbers whenever they are defined, i.e. whenever `I` has points
arbitrarily close to that side. -/
def PiecewiseContinuousOn (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ A : Finset ℝ, (↑A : Set ℝ) ⊆ I ∧ ContinuousOn f (I \ ↑A) ∧
    ∀ a ∈ A,
      ((𝓝[I ∩ Iio a] a).NeBot → ∃ l : ℝ, Tendsto f (𝓝[I ∩ Iio a] a) (𝓝 l)) ∧
      ((𝓝[I ∩ Ioi a] a).NeBot → ∃ l : ℝ, Tendsto f (𝓝[I ∩ Ioi a] a) (𝓝 l))

/-- Definition 5: `φ` is a Pólya frequency function of order `n` (`PF_n`) if
(a) `0 < ∫ φ < ∞` and (b) `det [φ(x_i - t_j)]_{1,k} ≥ 0` whenever `1 ≤ k ≤ n`,
`x₁ < ⋯ < x_k` and `t₁ < ⋯ < t_k`. Condition (b) with `k = 1` forces `φ ≥ 0`, so (a) is
Lebesgue integrability together with a positive integral. -/
def IsPF (n : ℕ) (φ : ℝ → ℝ) : Prop :=
  (Integrable φ ∧ 0 < ∫ x, φ x) ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n → ∀ x t : Fin k → ℝ, StrictMono x → StrictMono t →
      0 ≤ (Matrix.of fun i j : Fin k => φ (x i - t j)).det

/-- Definition 6: `φ` is a Pólya frequency function (`PFF`) if it is `PF_n` for all `n ≥ 1`. -/
def IsPFF (φ : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → IsPF n φ

/-- Definition 7: a `PFF` function with total integral `1` is a Pólya density. -/
def IsPolyaDensity (φ : ℝ → ℝ) : Prop :=
  IsPFF φ ∧ ∫ x, φ x = 1

/-- Definition 8: a Pólya density vanishing on `R⁻ = (-∞, 0)` is a one-sided Pólya density. -/
def IsOneSidedPolyaDensity (φ : ℝ → ℝ) : Prop :=
  IsPolyaDensity φ ∧ ∀ x : ℝ, x < 0 → φ x = 0

/-- §III / §VIII: `f` is PF-integrable if the convolution `f * ψ` exists (the integral is finite)
at every point whenever `ψ` is a Pólya frequency function. -/
def PFIntegrable (f : ℝ → ℝ) : Prop :=
  ∀ ψ : ℝ → ℝ, IsPFF ψ → ∀ y : ℝ, Integrable (fun ξ => f (y - ξ) * ψ ξ)

/-- Definition 1: `f` is non-`K`-decreasing on `X` if `f x ≤ f y + K` for `x, y ∈ X`, `x ≤ y`. -/
def NonKDecreasingOn (f : ℝ → ℝ) (K : ℝ) (X : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≤ y → f x ≤ f y + K

/-- Definition 2: the class `C_a(K)` (for `K ≥ 0`, `a ∈ ℝ`): functions `f` which, for some
`I ∈ {(-∞, a), (-∞, a]}`, are (i) piecewise continuous, (ii) PF-integrable, (iii) nonincreasing
on `I`, (iv) non-`K`-decreasing on `ℝ \ I`, and (v) satisfy `f x → ∞` as `|x| → ∞`. -/
def CaK (a K : ℝ) (f : ℝ → ℝ) : Prop :=
  0 ≤ K ∧ ∃ I : Set ℝ, (I = Iio a ∨ I = Iic a) ∧
    PiecewiseContinuousOn f univ ∧ PFIntegrable f ∧ AntitoneOn f I ∧
    NonKDecreasingOn f K Iᶜ ∧ Tendsto f (cocompact ℝ) atTop

/-- Definition 3: the class `C(K)` (for `K ≥ 0`): continuous functions lying in `C_a(K)` for
some `a ∈ ℝ`. -/
def CK (K : ℝ) (f : ℝ → ℝ) : Prop :=
  0 ≤ K ∧ Continuous f ∧ ∃ a : ℝ, CaK a K f

/-- Definition 10: `f` is quasi-`K`-convex on the convex set `X` if `x, y ∈ X`, `x ≤ y` and
`0 ≤ λ ≤ 1` imply `f(λx + (1-λ)y) ≤ max (f x) (f y + K)`  (27). -/
def QuasiKConvexOn (f : ℝ → ℝ) (K : ℝ) (X : Set ℝ) : Prop :=
  Convex ℝ X ∧ ∀ x ∈ X, ∀ y ∈ X, x ≤ y → ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
    f (l * x + (1 - l) * y) ≤ max (f x) (f y + K)

/-- Definition 4: an ordering policy function `y` (post-order inventory level as a function of the
pre-order level) is a generalized `(s, S)` policy if (i) `y x = x` for `s ≤ x` and
(ii) `y z ≥ y x ≥ S ≥ s` for `z < x < s`. -/
def IsGenSS (y : ℝ → ℝ) (s S : ℝ) : Prop :=
  (∀ x : ℝ, s ≤ x → y x = x) ∧
    (∀ z x : ℝ, z < x → x < s → y x ≤ y z ∧ S ≤ y x) ∧ s ≤ S

/-- The (negative) exponential density with parameter `lam`:
`lam * exp (-lam * t)` for `t ≥ 0` and `0` otherwise. -/
noncomputable def expDensity (lam : ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then lam * Real.exp (-lam * t) else 0

end PorteusSS


