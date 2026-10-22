-- Prove2me | Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Optimization
-- name    : KellyStochasticNetworks_RandomAccessCapacity_Optimization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:47:48.945082+00:00
-- url     : https://prove2.me/theorems/a7bb9468-a55b-4393-a04c-b574b9c48a84
-- title:
--   Extended value functions, supporting hyperplanes, and the Lagrangian
-- statement:
--   Let $X\subseteq\mathbb R^n$, let $f:\mathbb R^n\to\mathbb R$ be an objective, and let $h:\mathbb R^n\to\mathbb R^m$ be a constraint map. For a right-hand side $b$ and multiplier $y$ in $\mathbb R^m$, define
--
--   $$\phi_{=}(b)=\inf\{f(x):x\in X,\ h(x)=b\},\qquad
--   L(x;y)=f(x)+\sum_i y_i(b_i-h_i(x)),\qquad
--   g_b(y)=\inf_{x\in X}L(x;y).$$
--
--   The strong Lagrangian principle is the existence of a finite real multiplier vector $y$ with $\phi_{=}(b)=g_b(y)$. The inequality value function $\phi_{\le}(b)$ uses $h_i(x)\le b_i$ for every $i$; this is exactly the slack-variable problem $h(x)+z=b$, $z\ge0$.
--
--   For an extended-real function $\phi$, convexity means that its real epigraph $\{(c,t):\phi(c)\le t\}$ is convex. A nonvertical support at $b$ means there are a real height $a$ and real vector $y$ such that
--
--   $$\phi(b)=a,\qquad a+\sum_i y_i(c_i-b_i)\le\phi(c)\quad\text{for all }c.$$
--
--   These notions express the optimization infrastructure used in the capacity argument.
--
--   **Formalization Note** All infima take values in the extended real line: an empty feasible objective set gives $+\infty$ and an objective unbounded below gives $-\infty$. Affine expressions are evaluated in the reals before embedding in the extended reals. The strong principle follows the literal printed definition without an added finite-value assumption; the resulting issue in Theorem C.4 is recorded separately.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 207–209 (PDF pp. 215–217), Appendix C, P(b), (C.2), and support/strong-principle definitions. DOI: 10.1017/cbo9781139565363.

import Mathlib

namespace KellyStochasticNetworks.RandomAccessCapacity

/-- Convexity of an extended-valued function is convexity of its real epigraph. -/
def EpigraphConvex {m : ℕ} (φ : (Fin m → ℝ) → EReal) : Prop :=
  Convex ℝ {p : (Fin m → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)}

/-- A finite-height affine minorant touching at b; no arithmetic on infinities. -/
def HasNonverticalSupport {m : ℕ} (φ : (Fin m → ℝ) → EReal)
    (b : Fin m → ℝ) : Prop :=
  ∃ a : ℝ, ∃ y : Fin m → ℝ, φ b = (a : EReal) ∧
    ∀ c, ((a + ∑ i, y i * (c i - b i) : ℝ) : EReal) ≤ φ c

noncomputable def equalityValue {n m : ℕ} (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (h : (Fin n → ℝ) → Fin m → ℝ)
    (b : Fin m → ℝ) : EReal :=
  sInf {v : EReal | ∃ x ∈ X, h x = b ∧ v = (f x : EReal)}

noncomputable def lagrangian {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (h : (Fin n → ℝ) → Fin m → ℝ) (b y : Fin m → ℝ)
    (x : Fin n → ℝ) : ℝ := f x + ∑ i, y i * (b i - h x i)

noncomputable def dualValue {n m : ℕ} (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (h : (Fin n → ℝ) → Fin m → ℝ)
    (b y : Fin m → ℝ) : EReal :=
  sInf {v : EReal | ∃ x ∈ X, v = (lagrangian f h b y x : EReal)}

/-- The literal definition on printed p.208; no finite-value proviso is printed. -/
def StrongLagrangian {n m : ℕ} (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (h : (Fin n → ℝ) → Fin m → ℝ)
    (b : Fin m → ℝ) : Prop :=
  ∃ y : Fin m → ℝ, equalityValue X f h b = dualValue X f h b y

/-- (C.2), after eliminating z≥0 from h(x)+z=b. -/
noncomputable def inequalityValue {n m : ℕ} (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (h : (Fin n → ℝ) → Fin m → ℝ)
    (b : Fin m → ℝ) : EReal :=
  sInf {v : EReal | ∃ x ∈ X, (∀ i, h x i ≤ b i) ∧ v = (f x : EReal)}

end KellyStochasticNetworks.RandomAccessCapacity


