-- Prove2me | Definitions.Def_eulerMascheroni_rivoalForms
-- name    : eulerMascheroni_rivoalForms
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-25T21:11:22.817459+00:00
-- url     : https://prove2.me/theorems/0cc94702-27b3-4a2a-946d-2767fef8d372
-- title:
--   Rivoal's forms in $1,e,e\,\mathrm{Ein}(1)$: finite-sum coefficients
-- statement:
--   Explicit finite-sum coefficients of Rivoal's simultaneous approximations to $1$, $e$ and $\theta=e\operatorname{Ein}(1)$.
--
--   Fix $n\ge1$. Let $H_k=\sum_{i=1}^k 1/i$ be the harmonic numbers and $E_s=\sum_{l=0}^s 1/l!$. For $0\le j\le n$ put
--   $$
--   \beta_{n,j}=\frac{(3n-j)!}{\big(j!\,(n-j)!\big)^2},\qquad h_{n,j}=H_{3n-j}+2H_j-2H_{n-j}.
--   $$
--   The three coefficients are
--   $$
--   r'_n=\sum_{j=0}^n\beta_{n,j},\qquad q'_n=-\sum_{j=0}^n\beta_{n,j}h_{n,j},\qquad
--   p'_n=\sum_{i=0}^{n-1}E_{n-1-i}\Big(\beta_{n,i}h_{n,i}+\sum_{k=0}^{i-1}\frac{(-1)^{i-k}\beta_{n,k}}{(i-k)\,(i-k)!}\Big).
--   $$
--   The remainder is the alternating series
--   $$
--   S_n=\sum_{m\ge0}\frac{(-1)^m}{m!}\left(\frac{(m+2n)!}{(m+3n+1)!}\right)^2,
--   $$
--   and the common denominator is $d(3n)=\operatorname{lcm}(1,\dots,3n)$.
--
--   These data describe the linear forms $p'_n+q'_ne+r'_n\theta=e\,S_n$. Up to the sign $(-1)^{n+1}$ they are Rivoal's forms $e\cdot R_{n,0}(-1)$, written without integrals. They are used to prove that $1,e,e\operatorname{Ein}(1)$ are linearly independent over $\mathbb Q$. Small values: $(p'_1,q'_1,r'_1)=(-1,-6,8)$ and $(p'_2,q'_2,r'_2)=(-104,-411/2,306)$.
--
--   **Formalization Note** Everything is a function of natural numbers with values in $\mathbb Q$, except `remainder` (a real `tsum`) and `den` (a natural number, `Finset.lcm` of $1,\dots,3n$). Truncated subtraction only occurs with $j\le n$ in the intended range.
-- source:
--   T. Rivoal, On the arithmetic nature of the values of the gamma function, Euler's constant, and Gompertz's constant, Michigan Math. J. 61 (2012), Prop. 4 (eq. 3.5) and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); finite-sum expansion derived in research notes (Beta-integral series + partial fractions).

import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Rivoal's linear forms in `1, e, e·Ein(1)` (Rivoal, Michigan Math. J. 61 (2012), Prop. 4, at `z = -1`),
written with finite sums only.
-/

noncomputable section
namespace EulerMascheroni.Rivoal

/-- `β_{n,j} = (3n-j)! / (j! (n-j)!)²`. -/
def beta (n j : ℕ) : ℚ :=
  ((3 * n - j).factorial : ℚ) / (((j.factorial : ℚ) * ((n - j).factorial : ℚ)) ^ 2)

/-- `h_{n,j} = H_{3n-j} + 2 H_j - 2 H_{n-j}` (harmonic numbers). -/
def hcoef (n j : ℕ) : ℚ := harmonic (3 * n - j) + 2 * harmonic j - 2 * harmonic (n - j)

/-- `E_s = ∑_{l ≤ s} 1/l!`. -/
def expPartial (s : ℕ) : ℚ := ∑ l ∈ Finset.range (s + 1), ((l.factorial : ℚ))⁻¹

/-- Coefficient of `e·Ein(1)`: `r'_n = ∑_{j ≤ n} β_{n,j}`. -/
def rCoef (n : ℕ) : ℚ := ∑ j ∈ Finset.range (n + 1), beta n j

/-- Coefficient of `e`: `q'_n = -∑_{j ≤ n} β_{n,j} h_{n,j}`. -/
def qCoef (n : ℕ) : ℚ := -∑ j ∈ Finset.range (n + 1), beta n j * hcoef n j

/-- Constant coefficient `p'_n`. -/
def pCoef (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, expPartial (n - 1 - i) *
    (beta n i * hcoef n i +
      ∑ k ∈ Finset.range i,
        (-1 : ℚ) ^ (i - k) * beta n k / (((i - k : ℕ) : ℚ) * ((i - k).factorial : ℚ)))

/-- `S_n = ∑_{m ≥ 0} (-1)^m / m! · ((m+2n)! / (m+3n+1)!)²`. -/
def remainder (n : ℕ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ) ^ m / (m.factorial : ℝ) *
    (((m + 2 * n).factorial : ℝ) / ((m + 3 * n + 1).factorial : ℝ)) ^ 2

/-- `d(3n) = lcm(1, …, 3n)`. -/
def den (n : ℕ) : ℕ := (Finset.range (3 * n)).lcm (fun i => i + 1)

end EulerMascheroni.Rivoal


