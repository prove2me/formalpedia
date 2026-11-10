-- Prove2me | Definitions.Def_StableCountSub3_Savings
-- name    : StableCountSub3_Savings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:50:18.550118+00:00
-- url     : https://prove2.me/theorems/c4d30d01-7bae-4930-82bd-f77bdbef2701
-- title:
--   Geometric benchmark, $C_0$, tail-probability deficits, weights, $\delta_d$ and savings
-- statement:
--   The quantities of §§3.4 and 4 (natural logarithms):
--
--   - The geometric law at $x=U_m$: $P(G=k)=x(1-x)^k$ for $k=0,1,2,\dots$ (`geom`). The benchmark $E_{G_1,G_2}[\log(1+G_1+G_2)]$ for independent $G_1,G_2$ with this law is the series $\sum_{j,k\ge0}x(1-x)^j\,x(1-x)^k\log(1+j+k)$ (`benchmark`).
--   - $C_0=\sum_{j\ge1}\frac{2\log j}{(j+1)(j+2)}$ (end of the proof of Lemma 3.10).
--   - Definition 4.1, conditional on $D$ and $U_m=x$: $a_k=(1-x)^k-P(L\ge k)$, $b_k=(1-x)^k-P(R\ge k)$ (`deficitL`, `deficitR`), and $w_k=E_{G_1}\bigl[\log\frac{G_1+k+1}{G_1+k}\bigr]=\sum_{j\ge0}x(1-x)^j\log\frac{j+k+1}{j+k}$ (`weight`).
--   - Definition 4.3: $\delta_d=\sum_{j\ge d}\frac{2\log\frac{j+1}{j}}{(j+1)(j+2)(j+3)}$ for a positive integer $d$, and $t=\delta_4$ (`tCredit`, §6.1).
--   - `tailPow x s` is $(1-x)^{s-1}$, read as $0$ when $s=\infty$ (after Lemma 3.9).
--   - `savingAt` is the saving of Lemma 4.5 at a direction–depth pair $(\pm,d)$: $(1+\frac{d+1}{d+4})\delta_d$ if $s^\pm_{m,D}(d)\ge d+3$, $\delta_d$ if only $s^\pm_{m,D}(d)\ge d+2$, and $0$ otherwise.
--
--   For $x\in(0,1)$ and positive indices $k,d$, these series have nonnegative terms and converge. The summation indices are shifted to start at $0$.
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), §3.4, pp. 16–17 (PDF 18–19); Definitions 4.1, 4.3, pp. 20–22 (PDF 22–24); §6.1, p. 32 (PDF 34)

import Mathlib
import Definitions.Def_StableCountSub3_RandomReveal

open StableMatching

noncomputable section

namespace StableCountSub3

variable {n : ℕ}

/-- The geometric law of §3.4: given `x = U_m`, `P(G = k) = x (1 − x)^k` for `k = 0, 1, 2, …`
(the number of failures before the first success; `P(G ≥ k) = (1 − x)^k`). -/
def geom (x : ℝ) (k : ℕ) : ℝ := x * (1 - x) ^ k

/-- The geometric benchmark `E_{G₁,G₂}[log(1 + G₁ + G₂)]` at `U_m = x` (§3.4), for independent
`G₁, G₂` with the law `geom x`: the sum over `(j, k) ∈ ℕ²` of
`x(1−x)^j · x(1−x)^k · log(1 + j + k)` (nonnegative terms). -/
def benchmark (x : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, geom x p.1 * geom x p.2 * Real.log (1 + (p.1 : ℝ) + (p.2 : ℝ))

/-- `C₀ = ∑_{j ≥ 1} 2 log j / ((j + 1)(j + 2))` (end of the proof of Lemma 3.10), natural
logarithm; the summation index is shifted (`j = i + 1`). -/
def C0 : ℝ :=
  ∑' i : ℕ, 2 * Real.log ((i : ℝ) + 1) / (((i : ℝ) + 2) * ((i : ℝ) + 3))

/-- Definition 4.1: the weight `w_k = E_{G₁}[log((G₁ + k + 1)/(G₁ + k))]` at `U_m = x`. -/
def weight (x : ℝ) (k : ℕ) : ℝ :=
  ∑' j : ℕ, geom x j * Real.log (((j : ℝ) + k + 1) / ((j : ℝ) + k))

/-- Definition 4.1: the tail-probability deficit `a_k = (1 − x)^k − P(L ≥ k)` of
`L = L_m(D, U)`, conditional on `D` and `U_m = x`. -/
def deficitL (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (x : ℝ) (k : ℕ) : ℝ :=
  (1 - x) ^ k - probAt m x fun U => k ≤ Lm I D m U

/-- Definition 4.1: the tail-probability deficit `b_k = (1 − x)^k − P(R ≥ k)` of
`R = R_m(D, U)`, conditional on `D` and `U_m = x`. -/
def deficitR (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (x : ℝ) (k : ℕ) : ℝ :=
  (1 - x) ^ k - probAt m x fun U => k ≤ Rm I D m U

/-- Definition 4.3: `δ_d = ∑_{j ≥ d} 2 log((j + 1)/j) / ((j + 1)(j + 2)(j + 3))` for a positive
integer `d`; the summation index is shifted (`j = i + d`). -/
def delta (d : ℕ) : ℝ :=
  ∑' i : ℕ, 2 * Real.log (((i : ℝ) + d + 1) / ((i : ℝ) + d)) /
    (((i : ℝ) + d + 1) * ((i : ℝ) + d + 2) * ((i : ℝ) + d + 3))

/-- `t = δ₄` (§6.1). -/
def tCredit : ℝ := delta 4

/-- `(1 − x)^{s − 1}` for a support size `s ∈ ℕ ∪ {∞}`, read as `0` when `s = ∞`
(the convention stated after Lemma 3.9). -/
def tailPow (x : ℝ) (s : ℕ∞) : ℝ :=
  match s with
  | ⊤ => 0
  | (s : ℕ) => (1 - x) ^ (s - 1)

/-- The saving of Lemma 4.5 at the direction–depth pair `(dir, d)`, using only the stronger
saving when both conditions hold: `(1 + (d+1)/(d+4)) δ_d` if `s^dir_{m,D}(d) ≥ d + 3`,
`δ_d` if `s^dir_{m,D}(d) ≥ d + 2` only, and `0` otherwise. -/
def savingAt (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) (d : ℕ) : ℝ :=
  if ((d + 3 : ℕ) : ℕ∞) ≤ ssize I D m dir d then (1 + ((d : ℝ) + 1) / ((d : ℝ) + 4)) * delta d
  else if ((d + 2 : ℕ) : ℕ∞) ≤ ssize I D m dir d then delta d
  else 0

end StableCountSub3


