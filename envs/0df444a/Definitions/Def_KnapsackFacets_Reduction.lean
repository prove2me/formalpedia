-- Prove2me | Definitions.Def_KnapsackFacets_Reduction
-- name    : KnapsackFacets_Reduction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:23.511745+00:00
-- url     : https://prove2.me/theorems/07b76101-3fe7-4055-8dc5-1119031cd551
-- title:
--   The KNAPSACK FACETS instance (3)–(6) built from a CSS instance
-- statement:
--   Let $(w,t)$ be a CSS instance with $w\in\mathbb Z_+^n$, let $L=w([n])$, $r=\lceil\log_2(30L+20)-1\rceil$ and $N=2r+n+4$. The KNAPSACK FACETS instance of the proof of Theorem 4 is
--   $$
--   a_i=\begin{cases} tf_i, & i=1,\dots,2r+1,\\ t(2L+1)+1, & i=2r+2,\\ (t+1)w_{i-2r-2}, & i=2r+3,\dots,2r+n+2,\\ tf_{2r+1}+t^2+t(2L+2)+1, & i=2r+n+3,\\ t+1, & i=2r+n+4,\end{cases}
--   \qquad b=t\sum_{i=1}^{2r+1}f_i+t^2+t(2L+2)+1,
--   $$
--   $$
--   \alpha_i=\begin{cases} f_i, & i=1,\dots,2r+1,\\ 2L+2, & i=2r+2,\\ w_{i-2r-2}, & i=2r+3,\dots,2r+n+2,\\ f_{2r+1}+t+2L+1, & i=2r+n+3,\\ 0, & i=2r+n+4,\end{cases}
--   \qquad \beta=\sum_{i=1}^{2r+1}f_i+t+2L+1 .
--   $$
--
--   Every polyhedral step of the proof of Theorem 4 (Claims C and D, (i), (ii)) is a statement about this instance.
--
--   **Formalization Note** $t$ is a natural number (the proof assumes $t\ge2$). $r$ is `Nat.clog 2 (30L+20) - 1`, which equals $\lceil\log_2(30L+20)\rceil-1=\lceil\log_2(30L+20)-1\rceil\ge4$. The coefficient functions take the paper's 1-based index; the vectors $a,\alpha$ on `Fin N` have coordinate $i$ equal to the paper's $a_{i+1},\alpha_{i+1}$.
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, Theorem 4, proof, p.6, (3)–(6) and "Here N := 2r + n + 4"

import Definitions.Def_KnapsackFacets_ShiftedFib

set_option autoImplicit false

namespace KnapsackFacets

/-- **The parameter `r`** of the reduction as a function of `L`: `r = ⌈log₂(30L + 20) − 1⌉`.
Chen & Zhu, arXiv:2211.03311v3, proof of Theorem 4, p.6.

**Formalization Note.** `Nat.clog 2 m` is `⌈log₂ m⌉` for `m ≥ 1`, and
`⌈log₂(30L + 20) − 1⌉ = ⌈log₂(30L + 20)⌉ − 1 ≥ 4`, so the natural-number subtraction is exact. -/
def rOf (L : ℕ) : ℕ :=
  Nat.clog 2 (30 * L + 20) - 1

/-- **`L = w([n])`**, the total weight of a CSS instance. Chen & Zhu, arXiv:2211.03311v3,
proof of Theorem 4, p.6. -/
def redL {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  ∑ i, w i

/-- **`r`** of the reduction instance, `r = ⌈log₂(30L + 20) − 1⌉` with `L = w([n])`.
Chen & Zhu, arXiv:2211.03311v3, proof of Theorem 4, p.6. -/
def redR {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  rOf (redL w)

/-- **`N := 2r + n + 4`**, the dimension of the reduction instance. Chen & Zhu,
arXiv:2211.03311v3, proof of Theorem 4, p.6 ("Here N := 2r + n + 4 is the dimension of the
vectors a and α"). -/
def redN {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  2 * redR w + n + 4

/-- `wAt w j` is the weight `w_{j+1}` (0-based index `j`), and `0` for `j ≥ n` (never used). -/
def wAt {n : ℕ} (w : Fin n → ℕ) (j : ℕ) : ℕ :=
  if h : j < n then w ⟨j, h⟩ else 0

/-- **The coefficients `aᵢ` of (3)**, for the paper's 1-based index `i`. Chen & Zhu,
arXiv:2211.03311v3, proof of Theorem 4, p.6, (3):
`aᵢ = t fᵢ` (i = 1, …, 2r+1); `t(2L + 1) + 1` (i = 2r+2); `(t + 1) w_{i−2r−2}`
(i = 2r+3, …, 2r+n+2); `t f_{2r+1} + t² + t(2L + 2) + 1` (i = 2r+n+3); `t + 1` (i = 2r+n+4).

**Formalization Note.** The index `i` is the paper's 1-based index; the value `0` outside
`1, …, N` is never used. The CSS target `t` is a natural number here (the proof assumes
`t ≥ 2`). -/
def aCoef {n : ℕ} (w : Fin n → ℕ) (t i : ℕ) : ℕ :=
  if 1 ≤ i ∧ i ≤ 2 * redR w + 1 then t * shiftedFib i
  else if i = 2 * redR w + 2 then t * (2 * redL w + 1) + 1
  else if 2 * redR w + 3 ≤ i ∧ i ≤ 2 * redR w + n + 2 then
    (t + 1) * wAt w (i - (2 * redR w + 3))
  else if i = 2 * redR w + n + 3 then
    t * shiftedFib (2 * redR w + 1) + t ^ 2 + t * (2 * redL w + 2) + 1
  else if i = 2 * redR w + n + 4 then t + 1
  else 0

/-- **The coefficients `αᵢ` of (5)**, for the paper's 1-based index `i`. Chen & Zhu,
arXiv:2211.03311v3, proof of Theorem 4, p.6, (5):
`αᵢ = fᵢ` (i = 1, …, 2r+1); `2L + 2` (i = 2r+2); `w_{i−2r−2}` (i = 2r+3, …, 2r+n+2);
`f_{2r+1} + t + 2L + 1` (i = 2r+n+3); `0` (i = 2r+n+4).

**Formalization Note.** 1-based index; the value outside `1, …, N` is never used. All `αᵢ` of
the reduction are nonnegative, so they are natural numbers here and cast to `ℤ` in
`redAlpha`. -/
def alphaCoef {n : ℕ} (w : Fin n → ℕ) (t i : ℕ) : ℕ :=
  if 1 ≤ i ∧ i ≤ 2 * redR w + 1 then shiftedFib i
  else if i = 2 * redR w + 2 then 2 * redL w + 2
  else if 2 * redR w + 3 ≤ i ∧ i ≤ 2 * redR w + n + 2 then wAt w (i - (2 * redR w + 3))
  else if i = 2 * redR w + n + 3 then shiftedFib (2 * redR w + 1) + t + 2 * redL w + 1
  else 0

/-- **The capacity `b` of (4)**: `b = t Σ_{i=1}^{2r+1} fᵢ + t² + t(2L + 2) + 1`. Chen & Zhu,
arXiv:2211.03311v3, proof of Theorem 4, p.6, (4). -/
def redB {n : ℕ} (w : Fin n → ℕ) (t : ℕ) : ℕ :=
  t * ∑ i ∈ Finset.Icc 1 (2 * redR w + 1), shiftedFib i + t ^ 2 + t * (2 * redL w + 2) + 1

/-- **The right-hand side `β` of (6)**: `β = Σ_{i=1}^{2r+1} fᵢ + t + 2L + 1`. Chen & Zhu,
arXiv:2211.03311v3, proof of Theorem 4, p.6, (6). -/
def redBeta {n : ℕ} (w : Fin n → ℕ) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 (2 * redR w + 1), shiftedFib i + t + 2 * redL w + 1

/-- **The vector `a ∈ ℕᴺ` of (3)**, coordinate `i : Fin N` being the paper's `a_{i+1}`.
Chen & Zhu, arXiv:2211.03311v3, proof of Theorem 4, p.6. -/
def redA {n : ℕ} (w : Fin n → ℕ) (t : ℕ) : Fin (redN w) → ℕ :=
  fun i => aCoef w t (i.val + 1)

/-- **The vector `α ∈ ℤᴺ` of (5)**, coordinate `i : Fin N` being the paper's `α_{i+1}`.
Chen & Zhu, arXiv:2211.03311v3, proof of Theorem 4, p.6. -/
def redAlpha {n : ℕ} (w : Fin n → ℕ) (t : ℕ) : Fin (redN w) → ℤ :=
  fun i => (alphaCoef w t (i.val + 1) : ℤ)

end KnapsackFacets


