-- Prove2me | Definitions.Def_HighDimCLT_Hyperrect_Setting
-- name    : HighDimCLT_Hyperrect_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:37:44.077428+00:00
-- url     : https://prove2.me/theorems/a33a25ed-9916-486a-b816-97eead49c508
-- title:
--   §1–§2, §5, App. B, pp. 2309–2325 — normalized sums S^X_n, S^Y_n, covariance E[X_iX_i′], hyperrectangles (4), L_n, M_n(φ) (5), F_β, ϱ_n, ϱ′_n
-- statement:
--   The objects of the high-dimensional central limit theorem of Chernozhukov, Chetverikov and Kato.
--
--   Fix integers $n, p$ and write $\mathbb R^p$ for Euclidean space with coordinates indexed by $j = 1, \dots, p$. Let $X_1, \dots, X_n$ and $Y_1, \dots, Y_n$ be random vectors in $\mathbb R^p$ on a probability space $(\Omega, \mathcal F, \mathrm P)$, and write $X_{ij}$ for the $j$th coordinate of $X_i$.
--
--   1. **Second-moment matrix.** For a random vector $Z$ in $\mathbb R^p$, $\mathrm E[ZZ'] = (\mathrm E[Z_j Z_k])_{j,k}$. For centred $Z$ this is the covariance matrix, and $Y_i \sim N(0, \mathrm E[X_iX_i'])$ is the Gaussian vector with the covariance of $X_i$.
--   2. **Normalized sums.** $$S^X_n := \frac{1}{\sqrt n}\sum_{i=1}^n X_i, \qquad S^Y_n := \frac{1}{\sqrt n}\sum_{i=1}^n Y_i.$$
--   3. **Hyperrectangles** (display (4)). For $-\infty \le a_j \le b_j \le \infty$, $$A = \{w \in \mathbb R^p : a_j \le w_j \le b_j \text{ for all } j = 1, \dots, p\};$$ the class of all such sets is $\mathcal A^{\mathrm{re}}$.
--   4. **Third-moment parameter.** $$L_n := \max_{1 \le j \le p} \frac1n\sum_{i=1}^n \mathrm E\big[|X_{ij}|^3\big].$$
--   5. **Truncated maximal third moments** (display (5)). With $\max_j |x_j|$ the sup-norm of $x \in \mathbb R^p$, $$M_{n,X}(\phi) := \frac1n\sum_{i=1}^n \mathrm E\Big[\max_{1\le j\le p}|X_{ij}|^3\, 1\Big\{\max_{1\le j\le p}|X_{ij}| > \sqrt n/(4\phi\log p)\Big\}\Big],$$ $M_{n,Y}(\phi)$ is the same expression with $Y$ in place of $X$, and $M_n(\phi) := M_{n,X}(\phi) + M_{n,Y}(\phi)$.
--   6. **Smooth maximum** (Appendix B). For $\beta \ne 0$ and $y, w \in \mathbb R^p$, $$F_\beta(w) := \beta^{-1}\log\Big(\sum_{j=1}^p \exp\big(\beta(w_j - y_j)\big)\Big).$$
--   7. **Interpolation distances** (§5). With $w \le y$ meaning $w_j \le y_j$ for every $j$, $$\varrho_n := \sup_{y \in \mathbb R^p,\ v \in [0,1]} \big|\mathrm P(\sqrt v S^X_n + \sqrt{1-v} S^Y_n \le y) - \mathrm P(S^Y_n \le y)\big|,$$ $$\varrho_n' := \sup_{A \in \mathcal A^{\mathrm{re}},\ v \in [0,1]} \big|\mathrm P(\sqrt v S^X_n + \sqrt{1-v} S^Y_n \in A) - \mathrm P(S^Y_n \in A)\big|.$$
--
--   These are the quantities in which Theorem 2.1, Lemma 5.1, Corollary 5.1 and Proposition 2.1 are stated; $\log$ is the natural logarithm.
--
--   **Formalization Note** $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)`. The endpoints $a_j, b_j$ are extended reals (`EReal`), used only in comparisons. Maxima over $j$ are finite suprema (`⨆ j : Fin p`), which are true maxima for $p \ge 1$; every statement of the mission assumes $p \ge 3$. $M_{n,X}(\phi)$ is defined by formula (5) for every real $\phi$, not only for $\phi \ge 1$, because Theorem 2.1 evaluates it at $\phi_n$, which may be below $1$. $\varrho_n$ and $\varrho_n'$ are real suprema of families with values in $[0,1]$, hence true suprema; $\varrho_n'$ ranges over all endpoint vectors, and those with some $a_j > b_j$ give the empty set, whose term is $0$, so the supremum is unchanged. Expectations are Bochner integrals; the theorems that use $L_n$ and $M_n$ assume the integrability that makes them genuine expectations.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), pp. 2309–2312, §1, §1.1, §2 (4), (5); p. 2322, §5 (ϱ_n); p. 2323, §5 (ϱ′_n); p. 2325, App. B (F_β)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace HighDimCLT.Hyperrect

/-- The ambient space `ℝ^p`, as Euclidean space indexed by `Fin p`. -/
abbrev E (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- The matrix `E[Z Z']` of second moments of a random vector `Z` in `ℝ^p`
(its covariance matrix when `Z` is centred). -/
noncomputable def covMat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ}
    (Z : Ω → E p) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => ∫ ω, Z ω j * Z ω k ∂P

/-- The normalized sum `S_n = n^{-1/2} ∑_{i=1}^n X_i`. -/
noncomputable def normSum {Ω : Type*} {n p : ℕ} (X : Fin n → Ω → E p) (ω : Ω) : E p :=
  (Real.sqrt n)⁻¹ • ∑ i, X i ω

/-- The hyperrectangle `{w ∈ ℝ^p : lo_j ≤ w_j ≤ hi_j for all j}` with extended-real endpoints,
display (4). -/
def hyperrect {p : ℕ} (lo hi : Fin p → EReal) : Set (E p) :=
  {w | ∀ j, lo j ≤ ((w j : ℝ) : EReal) ∧ ((w j : ℝ) : EReal) ≤ hi j}

/-- `L_n = max_{1 ≤ j ≤ p} ∑_i E|X_ij|³ / n`. -/
noncomputable def Ln {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n p : ℕ}
    (X : Fin n → Ω → E p) : ℝ :=
  ⨆ j : Fin p, (∑ i, ∫ ω, |X i ω j| ^ 3 ∂P) / n

/-- `max_{1 ≤ j ≤ p} |x_j|` (a finite supremum, hence a maximum for `p ≥ 1`). -/
noncomputable def maxAbs {p : ℕ} (x : E p) : ℝ :=
  ⨆ j : Fin p, |x j|

/-- `M_{n,X}(φ) = n^{-1} ∑_i E[ max_j |X_ij|³ 1{max_j |X_ij| > √n / (4 φ log p)} ]`, display (5),
written for every real `φ`. -/
noncomputable def MnX {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n p : ℕ}
    (X : Fin n → Ω → E p) (φ : ℝ) : ℝ :=
  (∑ i, ∫ ω, (if Real.sqrt n / (4 * φ * Real.log p) < maxAbs (X i ω)
      then maxAbs (X i ω) ^ 3 else 0) ∂P) / n

/-- `M_n(φ) = M_{n,X}(φ) + M_{n,Y}(φ)`. -/
noncomputable def Mn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n p : ℕ}
    (X Y : Fin n → Ω → E p) (φ : ℝ) : ℝ :=
  MnX P X φ + MnX P Y φ

/-- The smooth max `F_β(w) = β^{-1} log ∑_j exp(β (w_j - y_j))` (App. B). -/
noncomputable def Fβ {p : ℕ} (β : ℝ) (y w : E p) : ℝ :=
  β⁻¹ * Real.log (∑ j, Real.exp (β * (w j - y j)))

/-- The interpolant `√v S^X_n + √(1 - v) S^Y_n`. -/
noncomputable def interp {Ω : Type*} {n p : ℕ} (X Y : Fin n → Ω → E p) (v : ℝ) (ω : Ω) : E p :=
  Real.sqrt v • normSum X ω + Real.sqrt (1 - v) • normSum Y ω

/-- `ϱ_n = sup_{y ∈ ℝ^p, v ∈ [0,1]} |P(√v S^X_n + √(1-v) S^Y_n ≤ y) − P(S^Y_n ≤ y)|` (§5).
Every term lies in `[0, 1]`, so the real supremum is the true supremum. -/
noncomputable def varrho {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n p : ℕ}
    (X Y : Fin n → Ω → E p) : ℝ :=
  ⨆ (y : E p) (v : Set.Icc (0 : ℝ) 1),
    |P.real {ω | ∀ j, interp X Y v ω j ≤ y j} - P.real {ω | ∀ j, normSum Y ω j ≤ y j}|

/-- `ϱ'_n = sup_{A ∈ 𝒜^re, v ∈ [0,1]} |P(√v S^X_n + √(1-v) S^Y_n ∈ A) − P(S^Y_n ∈ A)|` (§5).
The supremum runs over all endpoint vectors; those with some `lo_j > hi_j` give the empty set,
whose term is `0`, so they do not change the supremum. -/
noncomputable def varrho' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n p : ℕ}
    (X Y : Fin n → Ω → E p) : ℝ :=
  ⨆ (lo : Fin p → EReal) (hi : Fin p → EReal) (v : Set.Icc (0 : ℝ) 1),
    |P.real {ω | interp X Y v ω ∈ hyperrect lo hi} - P.real {ω | normSum Y ω ∈ hyperrect lo hi}|

end HighDimCLT.Hyperrect


