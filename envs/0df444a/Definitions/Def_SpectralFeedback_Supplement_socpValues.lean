-- Prove2me | Definitions.Def_SpectralFeedback_Supplement_socpValues
-- name    : SpectralFeedback_Supplement_socpValues
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:54:53.485593+00:00
-- url     : https://prove2.me/theorems/5e38039c-d522-4eb2-b636-cf4184e2c346
-- title:
--   Real hives $H_n(a,b;c)$, the hive chain (C.10) and the finite program of Theorem C.3
-- statement:
--   1. **Real hives.** For decreasing $a,b,c\in\mathbb R^n$, $H_n(a,b;c)$ is the system of real labels $H_{ij}$, $i,j\ge0$, $i+j\le n$, with $H_{00}=0$, boundary conditions (C.9)
--   $$
--   H_{i0}=\sum_{\ell\le i}a_\ell,\qquad H_{n-j,j}=\sum_\ell a_\ell+\sum_{\ell\le j}b_\ell,\qquad H_{0j}=\sum_{\ell\le j}c_\ell,
--   $$
--   and, for every base point $p$ and direction pair $(u,v)\in\{((1,0),(0,1)),((0,1),(-1,1)),((1,0),(1,-1))\}$ whose four vertices lie in the triangle, the rhombus inequality $H_{p+u}+H_{p+v}\ge H_p+H_{p+u+v}$ (§C.15.1).
--   2. **The hive chain (C.10).** Given $x,\lambda\in\mathbb R^n$: there are partial-sum spectra $s^1,\dots,s^m$, each decreasing and nonnegative, and real hives with $s^1=x$, $s^m=\lambda$ and $H_n(s^{h-1},x;s^h)$ for $2\le h\le m$. For $m=1$ there are no hives and $x=\lambda$.
--   3. **The program of Theorem C.3.** With $r'=\min\{r,n\}$, its feasible objective values are the numbers $mz$ over all decreasing nonnegative $x\in\mathbb R^n$ of trace $1/m$ satisfying the hive chain with spectrum $\lambda$, and $z\ge0$, $u_1,\dots,u_{r'}\ge0$ with
--   $$
--   z^2\le u_i(x_i+z)\ (1\le i\le r'),\qquad \sum_i u_i\le(r'-1)z \qquad\text{(C.8)}.
--   $$
--   The optimum of the program is the greatest element of this set.
--
--   **Formalization Note** Vectors are indexed 0-based by `Fin n`, so $\sum_{\ell\le i}$ is the sum over $\ell<i$. Labels form a function `ℕ → ℕ → ℝ`, and values outside the triangle are unconstrained. The three rhombus families are written out with their vertex ranges. In the chain, the paper's $s^h$ is `S (h-1)` and the hive of step $h$ is `H (h-1)`. The cone variables $u$ are indexed by `Fin (min r n)` and paired with the first $r'$ coordinates of $x$.
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Lemma C.2 (C.8), p.27 (PDF p.29); (C.9) and Theorem C.3 (C.10), p.28 (PDF p.30); §C.15.1, pp.44–45 (PDF pp.46–47)

import Mathlib

namespace SpectralFeedback

namespace Supplement

/-- **The real hive system `H_n(a, b; c)`** (Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), (C.9), p.28 (PDF p.30); §C.15.1,
pp.44–45 (PDF pp.46–47); Knutson–Tao [KT99, §2]): real labels `H_{ij}` on `i, j ≥ 0`, `i + j ≤ n`,
with `H_{00} = 0`, boundary values (C.9)
`H_{i0} = ∑_{ℓ≤i} a_ℓ`, `H_{n−j,j} = ∑_ℓ a_ℓ + ∑_{ℓ≤j} b_ℓ`, `H_{0j} = ∑_{ℓ≤j} c_ℓ`,
and, for every base point `p` and direction pair `(u, v)` among `((1,0),(0,1))`, `((0,1),(−1,1))`,
`((1,0),(1,−1))` whose four vertices lie in the triangle, the rhombus inequality
`H_{p+u} + H_{p+v} ≥ H_p + H_{p+u+v}`.

**Formalization Note** `a, b, c` are indexed 0-based by `Fin n`, so `∑_{ℓ≤i}` (1-based) is the sum
over `ℓ < i`. Labels are a function `ℕ → ℕ → ℝ`; values outside the triangle are unconstrained and
irrelevant. The three rhombus families are written out with their vertex ranges: for `p = (i, j)`,
type 1 needs `i + j + 2 ≤ n`; type 2 (`p + v = (i − 1, j + 1)`) needs `1 ≤ i`, `i + j + 1 ≤ n`;
type 3 (`p + v = (i + 1, j − 1)`) needs `1 ≤ j`, `i + j + 1 ≤ n`. -/
def IsHive (n : ℕ) (a b c : Fin n → ℝ) (H : ℕ → ℕ → ℝ) : Prop :=
  H 0 0 = 0 ∧
  (∀ i, i ≤ n → H i 0 = ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < i), a l) ∧
  (∀ j, j ≤ n → H (n - j) j =
    ∑ l, a l + ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j), b l) ∧
  (∀ j, j ≤ n → H 0 j = ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j), c l) ∧
  (∀ i j, i + j + 2 ≤ n → H i j + H (i + 1) (j + 1) ≤ H (i + 1) j + H i (j + 1)) ∧
  (∀ i j, 1 ≤ i → i + j + 1 ≤ n → H i j + H (i - 1) (j + 2) ≤ H i (j + 1) + H (i - 1) (j + 1)) ∧
  (∀ i j, 1 ≤ j → i + j + 1 ≤ n → H i j + H (i + 2) (j - 1) ≤ H (i + 1) j + H (i + 1) (j - 1))

/-- **The linear hive system (C.10)** (Qi, manuscript (Nov. 2026), Theorem C.3, (C.10), p.28
(PDF p.30)): given `x, λ ∈ ℝ^n`, there are partial-sum spectra `s^1, …, s^m` and real hives with
`s^1 = x`, `s^m = λ`, `H_n(s^{h−1}, x; s^h)` for `2 ≤ h ≤ m`, every partial spectrum decreasing and
nonnegative. For `m = 1` there are no hives and the system says `x = λ` (decreasing, nonnegative).

**Formalization Note** The paper's `s^h` (`1 ≤ h ≤ m`) is `S (h − 1)`; the hive for the paper's
step `h` (`2 ≤ h ≤ m`) is `H (h − 1)`. -/
def HiveChain (n m : ℕ) (x lam : Fin n → ℝ) : Prop :=
  ∃ S : ℕ → Fin n → ℝ, ∃ H : ℕ → ℕ → ℕ → ℝ,
    S 0 = x ∧ S (m - 1) = lam ∧
    (∀ h, h < m → Antitone (S h) ∧ 0 ≤ S h) ∧
    (∀ h, 1 ≤ h → h < m → IsHive n (S (h - 1)) x (S h) (H h))

/-- **The feasible objective values of the finite program of Theorem C.3** (Qi, *Spectral Structure
and Exact Arithmetic of Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026),
Theorem C.3, p.28 (PDF p.30), with Lemma C.2, (C.8), p.27 (PDF p.29)): the values `m z` over all
decreasing nonnegative `x ∈ ℝ^n` of trace `1/m` satisfying the hive system (C.10) with spectrum
`λ`, and `z ≥ 0`, `u_1, …, u_{r′} ≥ 0` with `z² ≤ u_i (x_i + z)` (`1 ≤ i ≤ r′`) and
`∑_i u_i ≤ (r′ − 1) z`, where `r′ = min{r, n}`.

**Formalization Note** `u` is indexed by `Fin (min r n)` and paired with the first `r′`
coordinates of `x` via `Fin.castLE`. The optimum of the program is the greatest element of this
set. -/
def socpValues (n m r : ℕ) (lam : Fin n → ℝ) : Set ℝ :=
  {v | ∃ x : Fin n → ℝ, ∃ z : ℝ, ∃ u : Fin (min r n) → ℝ,
    Antitone x ∧ 0 ≤ x ∧ ∑ i, x i = 1 / (m : ℝ) ∧ HiveChain n m x lam ∧
    0 ≤ z ∧ 0 ≤ u ∧
    (∀ i : Fin (min r n), z ^ 2 ≤ u i * (x (Fin.castLE (min_le_right r n) i) + z)) ∧
    ∑ i, u i ≤ (((min r n : ℕ) : ℝ) - 1) * z ∧
    v = (m : ℝ) * z}

end Supplement

end SpectralFeedback


