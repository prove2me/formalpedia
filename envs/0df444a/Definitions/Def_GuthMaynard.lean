-- Prove2me | Definitions.Def_GuthMaynard
-- name    : GuthMaynard
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-05T18:13:11.183141+00:00
-- url     : https://prove2.me/theorems/02de01ca-c062-4dae-955c-ea22d06dd219
-- title:
--   Dirichlet polynomials, additive energy and the sums S₁, S₂, S₃ (Guth–Maynard 2026)
-- statement:
--   The objects of Guth–Maynard's paper. Page numbers are those of arXiv:2405.20552v2. Lengths are integers, as the paper sets them (p. 3): “Given an integer $N \in \mathbb N$ and a sequence $(b_n)_{N<n\le 2N}$, a Dirichlet polynomial is a trigonometric sum of the form $$D(t) = \sum_{N<n\le 2N} b_ne^{it\log n}. \qquad (1.5)$$”
--
--   **Conventions (§1.2, p. 5).** “We write $A \ll B$ to mean that $|A| \le CB$ for an absolute constant $C$ … $A \sim B$ to mean $B < A \le 2B$. Similarly, we write $A \lessapprox B$ to mean that for any $\epsilon > 0$, there is a constant $C(\epsilon) > 0$ depending only on $\epsilon$ such that $|A| \le C(\epsilon)T^\epsilon B$ for all large $T$ … Asymptotic quantities such as $o(1)$ are interpreted as $T \to \infty$.” These are not definitions here: each statement spells out its quantifiers in this sense. “We use $e(x) := e^{2\pi ix}$ to denote the complex exponential.”
--
--   **Separation.** Theorem 1.1 (p. 1) speaks of “a sequence of $1$-separated points in $[0, T]$”, and §3 onward of “$T^\epsilon$-separated” sets. `IsSeparated δ W` says that distinct points of the finite set $W$ are at distance at least $\delta$. "Separated" is read with $\ge$, the usual meaning in this literature (Mathlib's `Metric.IsSeparated` is strict).
--
--   **Additive energy (1.7), pp. 4–5.** “For a finite set $W$, let $$E(W) := \#\{w_1, w_2, w_3, w_4 \in W : |w_1 + w_2 - w_3 - w_4| \le 1\}.$$” `energy W` counts ordered quadruples, repetitions allowed.
--
--   **Dyadic ranges (§1.2).** `dyadic M` is the set of integers $m$ with $m \sim M$, that is $M < m \le 2M$.
--
--   **The weight (p. 9).** “Throughout the rest of the paper we fix a smooth function $w : \mathbb R \to \mathbb R_{\ge 0}$ supported on $[1, 2]$ with $\|w^{(j)}\|_\infty = O_j(1)$ for all $j \in \mathbb Z_{\ge 0}$ and with $w(t) = 1$ for $t \in [6/5, 9/5]$.”
--   - `IsWeight w` lists these conditions, with smoothness as `ContDiff ℝ (⊤ : ℕ∞)` (infinitely differentiable).
--   - The derivative bounds $O_j(1)$ hold automatically for one fixed smooth compactly supported $w$.
--   - Statements about $D_N$, $M_W$, $\widehat h_t$ and the $S_k$ quantify over every $w$ with `IsWeight w`, with constants allowed to depend on $w$, which is the meaning of "we fix".
--
--   **The smoothed polynomial and the matrix (p. 10).** “We will work with the smoothed version $D_N(t)$ of $D(t)$ from Proposition 3.1 $$D_N(t) := \sum_n w\Big(\frac nN\Big)b_nn^{it}, \qquad (4.1)$$ where $w$ is the smooth bump supported on $[1, 2]$ defined in Section 3. Similarly, given a set $W \subseteq \mathbb R$, let $M_W$ be the $|W| \times N$ matrix with smoothed entries $$(M_W)_{t,n} = w(n/N)n^{it}, \qquad (4.2)$$ where $t \in W$ and $n \sim N$.”
--   - `smoothedPoly w N b t` sums over $N \le n \le 2N$, which contains every $n$ with $w(n/N) \ne 0$.
--   - `weightMatrix w N W` has columns $N < n \le 2N$, as printed. The two ranges differ only at $n = N$, where $w(1) = 0$.
--   - Lemma 4.1 (p. 10) names “$s_1(M_W)$ its largest singular value”. `topSingularValue A` is the first singular value of the linear map between Euclidean spaces that $A$ defines.
--
--   **The Fourier transforms $\widehat h_t$ ((4.4), p. 13).** “we introduce the function $$h_t(u) := w(u)^2u^{it}, \qquad (4.4)$$ which appears in the sums defining the coefficients of $M_WM_W^*$.” The proof of Lemma 4.3 writes $\widehat h_t(\xi) = \int e(-\xi u)h_t(u)\,du$. `hHat w t ξ` is Mathlib's Fourier transform `𝓕` of $h_t$ at $\xi$, which has exactly this normalization.
--
--   **The terms $I_m$ (Lemma 4.5, p. 14).** “Let $W$ be $T^\epsilon$-separated. Then we have $$\operatorname{tr}((M_WM_W^*)^3) = N^3|W|\|w\|_{L^2}^6 + \sum_{m\in\mathbb Z^3\setminus\{0\}} I_m + O_\epsilon(T^{-100}),$$ where $$I_m := N^3\sum_{t_1,t_2,t_3\in W}\widehat h_{t_1-t_2}(m_1N)\,\widehat h_{t_2-t_3}(m_2N)\,\widehat h_{t_3-t_1}(m_3N).$$” This is `Iterm w N W m`, for $m \in \mathbb Z^3$ written as `Fin 3 → ℤ`.
--
--   **The sums $S_1, S_2, S_3$ ((5.5), p. 16).** “we divide the sum into pieces $$\sum_{m\in\mathbb Z^3\setminus\{0\}} I_m = S_1 + S_2 + S_3, \qquad (5.5)$$ where $S_1$ contains the terms where exactly one $m_i$ is non-zero, $S_2$ contains the terms where exactly two $m_i$ are non-zero, and $S_3$ contains the terms where all three $m_i$ are non-zero.” `S k w N W` is the sum of $I_m$ over the $m$ with exactly $k$ nonzero coordinates, so $S_1$, $S_2$, $S_3$ are `S 1 w N W`, `S 2 w N W`, `S 3 w N W`.
--
--
--   **$J(f)$ (p. 29).** “Given $M > 0$ and a compactly supported smooth function $f$, we define $$J(f) := \sup_{0<M_1,M_2,M_3<M}\int\Big(\sum_{|m_1|\sim M_1,\ m_2\sim M_2,\ |m_3|\ll M_3} f\Big(\frac{m_1u + m_3}{m_2}\Big)\Big)^2du$$”.
--   - `J M K f` reads the range "$|m_3| \ll M_3$" as $|m_3| \le KM_3$, with $K$ the implied constant made an explicit parameter.
--   - It takes values in $[0, \infty]$: the integrand is a square, and the supremum needs no boundedness assumption there.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), pp. 1–29, the objects of Theorem 1.1 (p. 1), the additive energy (1.7) and the conventions of §1.2 (p. 5), the weight w (p. 9), D_N, M_W and s₁ ((4.1)–(4.2), p. 10), h_t and its Fourier transform ((4.4), p. 13), I_m (Lemma 4.5, p. 14), S₁, S₂, S₃ ((5.5), p. 16) and J(f) (p. 29)

import Mathlib

/-!
# Guth–Maynard, New large value estimates for Dirichlet polynomials

Objects from L. Guth and J. Maynard, *New large value estimates for Dirichlet polynomials*,
Ann. of Math. (2) 203 (2026), arXiv:2405.20552v2 (page numbers are those of arXiv v2).

* `IsSeparated δ W`: distinct points of `W` are at distance at least `δ` (pp. 1, 9).
* `energy W`: the additive energy `E(W)` of (1.7), p. 5.
* `dyadic M`: the integers `m` with `M < m ≤ 2M` (`m ∼ M`, §1.2, p. 5).
* `IsWeight w`: the conditions on the fixed weight `w` of §3, p. 9.
* `smoothedPoly w N b t`: `D_N(t)` of (4.1), p. 10.
* `weightMatrix w N W`: the matrix `M_W` of (4.2), p. 10, and `topSingularValue A`: `s₁(A)`.
* `hHat w t ξ`: the Fourier transform of `h_t(u) = w(u)² u^{it}` of (4.4), p. 13.
* `Iterm w N W m`: `I_m` of Lemma 4.5, p. 14, and `S k w N W` (`S₁`, `S₂`, `S₃` of (5.5), p. 16).
* `J M K f`: `J(f)` of §9, p. 29.
-/

namespace GuthMaynard

open Complex MeasureTheory FourierTransform
open scoped ENNReal

/-- `W` is `δ`-separated: distinct points of `W` are at distance at least `δ`. -/
def IsSeparated (δ : ℝ) (W : Finset ℝ) : Prop :=
  ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → δ ≤ |t - t'|

/-- The additive energy `E(W) = #{(w₁, w₂, w₃, w₄) ∈ W⁴ : |w₁ + w₂ - w₃ - w₄| ≤ 1}` of (1.7). -/
noncomputable def energy (W : Finset ℝ) : ℕ :=
  ((W ×ˢ W ×ˢ W ×ˢ W).filter fun p => |p.1 + p.2.1 - p.2.2.1 - p.2.2.2| ≤ 1).card

/-- The integers `m` with `M < m ≤ 2M`. -/
noncomputable def dyadic (M : ℝ) : Finset ℤ :=
  Finset.Ioc ⌊M⌋ ⌊2 * M⌋

/-- The conditions on the weight `w` fixed in §3: a smooth function `ℝ → [0, ∞)` supported on
`[1, 2]` and equal to `1` on `[6/5, 9/5]`. -/
structure IsWeight (w : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) w
  nonneg : ∀ x, 0 ≤ w x
  support_subset : Function.support w ⊆ Set.Icc 1 2
  eq_one : ∀ x ∈ Set.Icc (6 / 5 : ℝ) (9 / 5), w x = 1

/-- The smoothed Dirichlet polynomial `D_N(t) = ∑ₙ w(n/N) bₙ n^{it}` of (4.1). The sum runs over
`N ≤ n ≤ 2N`, which contains every `n` with `w(n/N) ≠ 0`. -/
noncomputable def smoothedPoly (w : ℝ → ℝ) (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc N (2 * N), (w ((n : ℝ) / N) : ℂ) * b n * (n : ℂ) ^ ((t : ℂ) * I)

/-- The `|W| × N` matrix `M_W` of (4.2): rows `t ∈ W`, columns `N < n ≤ 2N`, entries
`w(n/N) n^{it}`. -/
noncomputable def weightMatrix (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) :
    Matrix W (Finset.Ioc N (2 * N)) ℂ :=
  fun t n => (w ((n : ℝ) / N) : ℂ) * ((n : ℕ) : ℂ) ^ (((t : ℝ) : ℂ) * I)

/-- The largest singular value `s₁(A)` of a complex matrix, the first singular value of the linear
map `A` defines between Euclidean spaces. -/
noncomputable def topSingularValue {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues 0

/-- `ĥ_t(ξ) = ∫ e(-ξu) h_t(u) du` for `h_t(u) = w(u)² u^{it}` (4.4), with `e(x) = e^{2πix}`. -/
noncomputable def hHat (w : ℝ → ℝ) (t ξ : ℝ) : ℂ :=
  𝓕 (fun u : ℝ => ((w u ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I)) ξ

/-- `I_m = N³ ∑_{t₁,t₂,t₃ ∈ W} ĥ_{t₁-t₂}(m₁N) ĥ_{t₂-t₃}(m₂N) ĥ_{t₃-t₁}(m₃N)` of Lemma 4.5. -/
noncomputable def Iterm (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) : ℂ :=
  (N : ℂ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
    hHat w (t₁ - t₂) (m 0 * N) * hHat w (t₂ - t₃) (m 1 * N) * hHat w (t₃ - t₁) (m 2 * N)

/-- `S_k`: the sum of `I_m` over the `m ∈ ℤ³` with exactly `k` nonzero coordinates (5.5). -/
noncomputable def S (k : ℕ) (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) : ℂ :=
  ∑' m : {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = k}, Iterm w N W m

/-- `J(f)` of §9: the supremum over `0 < M₁, M₂, M₃ < M` of
`∫ (∑_{|m₁| ∼ M₁, m₂ ∼ M₂, |m₃| ≤ K M₃} f((m₁u + m₃)/m₂))² du`. The source writes the range of
`m₃` as `|m₃| ≪ M₃`; `K` is the implied constant. -/
noncomputable def J (M K : ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (M₁ : ℝ) (_ : M₁ ∈ Set.Ioo 0 M) (M₂ : ℝ) (_ : M₂ ∈ Set.Ioo 0 M) (M₃ : ℝ)
    (_ : M₃ ∈ Set.Ioo 0 M),
    ∫⁻ u : ℝ, ENNReal.ofReal
      ((∑ m₁ ∈ dyadic M₁ ∪ (dyadic M₁).map (Equiv.neg ℤ).toEmbedding, ∑ m₂ ∈ dyadic M₂,
          ∑ m₃ ∈ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋,
            f ((m₁ * u + m₃) / m₂)) ^ 2)

end GuthMaynard


