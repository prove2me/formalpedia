-- Prove2me | Definitions.Def_JacodTodorov10_LLN_Scheme
-- name    : JacodTodorov10_LLN_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:29.063425+00:00
-- url     : https://prove2.me/theorems/f9852d8b-34a2-49d4-850b-804839da00dc
-- title:
--   §3 — the sampling scheme (3.3), increments (3.2), local volatility estimators (3.4), U(F, kₙ) (3.5), U(F) (3.1) and the family 𝓡 (3.6)
-- statement:
--   The process $X$ is observed at the times $i\Delta_n$, $i\in\mathbb N$. A scheme consists of a mesh $\Delta_n>0$, a truncation level $u_n>0$ and a window size $k_n\ge1$.
--
--   1. **Condition (3.3).** For exponents $0<\varpi<\tfrac12$ and $0<\rho<1$ and some constant $K$, for all $n$,
--   $$\frac1K\le\frac{u_n}{\Delta_n^{\varpi}}\le K,\qquad \frac1K\le k_n\Delta_n^{\rho}\le K,$$
--   and $\Delta_n\to0$.
--   2. **Increments (3.2).** $\Delta^n_iY=Y_{i\Delta_n}-Y_{(i-1)\Delta_n}$ for $i\ge1$, and $\Delta^n_iY=0$ for $i\le0$.
--   3. **Local volatility estimators (3.4).**
--   $$\widehat c(k_n)_i=\frac1{k_n\Delta_n}\sum_{j=1}^{k_n}|\Delta^n_{i+j}X|^2\,1_{\{|\Delta^n_{i+j}X|\le u_n\}}.$$
--   4. **The observable statistic (3.5).**
--   $$U(F,k_n)_t=\sum_{i=k_n+1}^{[t/\Delta_n]-k_n}F\big(\Delta^n_iX,\ \widehat c(k_n)_{i-k_n-1},\ \widehat c(k_n)_i\big)\,1_{\{|\Delta^n_iX|>u_n\}}.$$
--   5. **The jump functional (3.1).**
--   $$U(F)_t=\sum_{s\le t}F(\Delta X_s,c_{s-},c_s)\,1_{\{\Delta X_s\neq0\}}.$$
--   6. **The family $\mathcal R$ (3.6).** With $D=\{x:\mathbb P(\exists s>0\text{ with }\Delta X_s=x)>0\}$, a set $R\subseteq\mathbb R$ belongs to $\mathcal R$ iff $R$ is open, has a finite complement, and $D\subseteq R$.
--
--   $U(F,k_n)$ is computable from the observations; Theorem 3.1 says that it estimates the unobservable $U(F)$.
--
--   **Formalization Note** The index $i$ of $\Delta^n_i$ and $\widehat c(k_n)_i$ ranges over $\mathbb Z$, so that $\widehat c(k_n)_{i-k_n-1}$ needs no truncated subtraction; observation times are $\max(i\Delta_n,0)$. The increment and the estimator are also available for a single mesh $\Delta$, window $k$ and cutoff $u$, as used in (8.11) and (8.14). The range of (3.5) is empty when $[t/\Delta_n]<2k_n+1$, as on the page. $U(F)_t$ is a `tsum` over the jump times $0<s\le t$; it is meaningful when the family is summable, which Theorem 3.1 asserts. $\mathbb P$ in $D$ is the outer measure. $\Delta_n\to0$ is not written in (3.3); it is the paper's standing regime (abstract; p. 2) and is needed for $u_n\to0$ and $k_n\to\infty$. Note that $0\in D$ (every $s$ at which $X$ does not jump has $\Delta X_s=0$), as the definition is printed.
-- source:
--   Jacod, Todorov, Do price and volatility jump together?, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §3, pp. 4–5 ((3.1)–(3.6)); §8.1, p. 26 (the convention Δⁿᵢ Y = 0 for i ≤ 0)

import Mathlib
import Definitions.Def_JacodTodorov10_LLN_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace JacodTodorov10.LLN

/-- The sampling scheme of arXiv:1010.4990v1, §3, p. 4: at stage `n` the process is observed at the
times `iΔ_n`, `u_n` is the truncation (cutoff) level and `k_n` the window size. -/
structure Scheme where
  /-- the mesh `Δ_n` -/
  Δ : ℕ → ℝ
  /-- the cutoff level `u_n` -/
  u : ℕ → ℝ
  /-- the window size `k_n` -/
  k : ℕ → ℕ

/-- **Condition (3.3)** (arXiv:1010.4990v1, §3, p. 4) with exponents `ϖ`, `ρ`: `Δ_n > 0`, `u_n > 0`,
`k_n ≥ 1`, `Δ_n → 0`, `0 < ϖ < 1/2`, `0 < ρ < 1`, and for some constant `K`,
`1/K ≤ u_n / Δ_n^ϖ ≤ K` and `1/K ≤ k_n Δ_n^ρ ≤ K` for all `n`.

Formalization Note: `Δ_n → 0` is not written in (3.3); it is the paper's standing high-frequency
regime ("as the mesh Δ_n goes to 0", abstract; "Δ_n → 0", p. 2), without which (3.3) does not force
`u_n → 0` or `k_n → ∞`. -/
def Scheme.Cond33 (S : Scheme) (ϖ ρ : ℝ) : Prop :=
  (∀ n, 0 < S.Δ n) ∧ (∀ n, 0 < S.u n) ∧ (∀ n, 1 ≤ S.k n) ∧ Tendsto S.Δ atTop (𝓝 0) ∧
    0 < ϖ ∧ ϖ < 1 / 2 ∧ 0 < ρ ∧ ρ < 1 ∧
    ∃ K : ℝ, ∀ n, 1 / K ≤ S.u n / S.Δ n ^ ϖ ∧ S.u n / S.Δ n ^ ϖ ≤ K ∧
      1 / K ≤ (S.k n : ℝ) * S.Δ n ^ ρ ∧ (S.k n : ℝ) * S.Δ n ^ ρ ≤ K

/-- The increment `Δ^n_i Y = Y_{iΔ} − Y_{(i−1)Δ}` of (3.2) (arXiv:1010.4990v1, p. 4) for a mesh
`Δ`, indexed by `i ∈ ℤ` with the convention `Δ^n_i Y = 0` for `i ≤ 0` (p. 26, after (8.6)). -/
noncomputable def incr {Ω : Type*} (Δ : ℝ) (Y : ℝ≥0 → Ω → ℝ) (i : ℤ) (ω : Ω) : ℝ :=
  if 1 ≤ i then Y (Real.toNNReal (i * Δ)) ω - Y (Real.toNNReal ((i - 1) * Δ)) ω else 0

/-- The local volatility estimator `ĉ(k)_i = (1/(kΔ)) ∑_{j=1}^{k} |Δ_{i+j} X|² 1_{|Δ_{i+j} X| ≤ u}`
of (3.4) (arXiv:1010.4990v1, p. 4), for mesh `Δ`, window `k` and cutoff `u`, indexed by `i ∈ ℤ`
(the convention `Δ_i X = 0` for `i ≤ 0` extends it to `i ≤ 0`, p. 26). -/
noncomputable def chat {Ω : Type*} (Δ u : ℝ) (k : ℕ) (X : ℝ≥0 → Ω → ℝ) (i : ℤ) (ω : Ω) : ℝ :=
  1 / (k * Δ) * ∑ j ∈ Finset.Icc 1 k,
    incr Δ X (i + j) ω ^ 2 * (if |incr Δ X (i + j) ω| ≤ u then 1 else 0)

/-- `ĉ(k_n)_i` at stage `n` of the scheme `S`. -/
noncomputable def Scheme.chat {Ω : Type*} (S : Scheme) (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (i : ℤ)
    (ω : Ω) : ℝ :=
  JacodTodorov10.LLN.chat (S.Δ n) (S.u n) (S.k n) X i ω

/-- `Δ^n_i X` at stage `n` of the scheme `S`. -/
noncomputable def Scheme.incr {Ω : Type*} (S : Scheme) (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (i : ℤ)
    (ω : Ω) : ℝ :=
  JacodTodorov10.LLN.incr (S.Δ n) X i ω

/-- The observable statistic of (3.5) (arXiv:1010.4990v1, p. 5):
`U(F, k_n)_t = ∑_{i = k_n+1}^{[t/Δ_n] − k_n} F(Δ^n_i X, ĉ(k_n)_{i−k_n−1}, ĉ(k_n)_i) 1_{|Δ^n_i X| > u_n}`.
The range is empty when `[t/Δ_n] < 2k_n + 1`. -/
noncomputable def UFk {Ω : Type*} (S : Scheme) (X : ℝ≥0 → Ω → ℝ) (F : ℝ → ℝ → ℝ → ℝ) (n : ℕ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Icc (S.k n + 1) (⌊(t : ℝ) / S.Δ n⌋₊ - S.k n),
    F (S.incr X n i ω) (S.chat X n ((i : ℤ) - S.k n - 1) ω) (S.chat X n i ω) *
      (if S.u n < |S.incr X n i ω| then 1 else 0)

/-- The jump functional of (3.1) (arXiv:1010.4990v1, p. 4):
`U(F)_t = ∑_{s ≤ t} F(ΔX_s, c_{s−}, c_s) 1_{ΔX_s ≠ 0}`, a sum over the jump times `0 < s ≤ t` of `X`
(`ΔX_0 = 0`). It is a `tsum`, meaningful when the family is summable; Theorem 3.1 asserts that. -/
noncomputable def UF {Ω : Type*} (X σ : ℝ≥0 → Ω → ℝ) (F : ℝ → ℝ → ℝ → ℝ) (t : ℝ≥0) (ω : Ω) :
    ℝ :=
  ∑' s : {s : ℝ≥0 // 0 < s ∧ s ≤ t ∧ pjump X s ω ≠ 0},
    F (pjump X s ω) (cLeft σ s ω) (c σ s ω)

/-- The set `D = {x : P(∃ s > 0 with ΔX_s = x) > 0}` of (3.6) (arXiv:1010.4990v1, p. 5); `P` is
applied as an outer measure. -/
def Dset {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Set ℝ :=
  {x : ℝ | 0 < P {ω | ∃ s : ℝ≥0, 0 < s ∧ pjump X s ω = x}}

/-- The family `𝓡` of (3.6) (arXiv:1010.4990v1, p. 5): `R ∈ 𝓡` iff `R` is open with a finite
complement and `D ⊆ R`. -/
def InR {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (R : Set ℝ) : Prop :=
  IsOpen R ∧ Rᶜ.Finite ∧ Dset P X ⊆ R

end JacodTodorov10.LLN


