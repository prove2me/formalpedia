-- Prove2me | Definitions.Def_KramerSaglam_TailSeries
-- name    : KramerSaglam_TailSeries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:03:28.397499+00:00
-- url     : https://prove2.me/theorems/80bd5c2e-be7b-4249-8db4-86f4cc7dc4af
-- title:
--   The divergence tails $b_N, s_N(u)$ and the series $T_N, B_N, G_N, C_N, e_N, R_N, J(w), c_N(u)$
-- statement:
--   The series of §3.3. Write $\tau_k = \dfrac{1}{2k(2k-1)}$. For integers $N\ge1$ the **divergence tails** are
--   $$
--   b_N = \sum_{k>N}\tau_k,\qquad s_N(u) = \sum_{k>N}u^{2k}\tau_k ,
--   $$
--   and $b_0 = 1$ as a separate convention. Then
--   $$
--   T_N=\sum_{i=0}^{N-1}b_i,\quad B_N=\sum_{i=0}^{N-1}b_ib_{N-i},\quad G_N(u)=\sum_{i=0}^{N-1}b_is_{N-i}(u),\quad C_N(u)=\sum_{k=1}^{N}(1-u^{2k})\tau_k,
--   $$
--   $$
--   e_N=\frac12\sum_{k=1}^N\frac1{2k-1},\qquad R_N=2T_N-1,
--   $$
--   $$
--   J(w)=\frac{55}{72}-\frac{31w^4}{8}+\frac{9w^8}{8}-\frac{w^{12}}{8}+\frac{38\,s_2(w)}{w},\qquad c_N(u)=C_N(u)+\frac{4G_N(u)}{u}-2B_N .
--   $$
--
--   The coefficients $c_N(u)$ are those of the expansion in $r=\rho^2$ that proves the three-bit inequality (Lemma 3.9); their positivity is the last step of the proof.
--
--   **Formalization Note** The tails are defined by their series (`tsum`); the integral forms on p.8 are not used. At $N=0$ the series would give $\ln 2$, not the convention $b_0=1$, so $b$ is defined by cases. $J(w)$ and $c_N(u)$ divide by $w$, $u$; the page's domains $0<w<1$ and $0<u\le1$ are assumed by the statements.
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), §3.3 p.8 (b_N, s_N, T_N, B_N, G_N, C_N), p.9 (e_N, R_N), p.10 (J), p.11 (c_N)

import Mathlib

open Finset

namespace KramerSaglam

/-!
# Divergence tails of §3.3

D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), pp.8–11.
-/

/-- The term `1 / (2k(2k − 1))` of the binary divergence series. -/
noncomputable def tailTerm (k : ℕ) : ℝ := 1 / ((2 * (k : ℝ)) * (2 * (k : ℝ) - 1))

/-- `b_N` (p.8): the tail `∑_{k>N} 1/(2k(2k−1))` for `N ≥ 1`, and `b_0 = 1` "as a separate convention".
**Formalization Note.** The page also gives the integral form `∫₀¹ x^{2N}/(1+x) dx`; the series is the
definition here. At `N = 0` the series would give `ln 2`, not `1`. -/
noncomputable def b (N : ℕ) : ℝ :=
  if N = 0 then 1 else ∑' k : ℕ, tailTerm (N + 1 + k)

/-- `s_N(u) = ∑_{k>N} u^{2k}/(2k(2k−1))` (p.8). -/
noncomputable def s (N : ℕ) (u : ℝ) : ℝ :=
  ∑' k : ℕ, u ^ (2 * (N + 1 + k)) * tailTerm (N + 1 + k)

/-- `T_N = ∑_{i=0}^{N−1} b_i` (p.8). -/
noncomputable def T (N : ℕ) : ℝ := ∑ i ∈ range N, b i

/-- `B_N = ∑_{i=0}^{N−1} b_i b_{N−i}` (p.8). -/
noncomputable def BB (N : ℕ) : ℝ := ∑ i ∈ range N, b i * b (N - i)

/-- `G_N(u) = ∑_{i=0}^{N−1} b_i s_{N−i}(u)` (p.8). -/
noncomputable def G (N : ℕ) (u : ℝ) : ℝ := ∑ i ∈ range N, b i * s (N - i) u

/-- `C_N(u) = ∑_{k=1}^{N} (1 − u^{2k})/(2k(2k−1))` (p.8). -/
noncomputable def CC (N : ℕ) (u : ℝ) : ℝ := ∑ k ∈ Icc 1 N, (1 - u ^ (2 * k)) * tailTerm k

/-- `e_N = (1/2) ∑_{k=1}^{N} 1/(2k−1)` (p.9). -/
noncomputable def e (N : ℕ) : ℝ := (1 / 2) * ∑ k ∈ Icc 1 N, 1 / (2 * (k : ℝ) - 1)

/-- `R_N = 2T_N − 1` (p.9). -/
noncomputable def R (N : ℕ) : ℝ := 2 * T N - 1

/-- `J(w) = 55/72 − 31w⁴/8 + 9w⁸/8 − w¹²/8 + 38 s₂(w)/w` (p.10). -/
noncomputable def JJ (w : ℝ) : ℝ :=
  55 / 72 - 31 * w ^ 4 / 8 + 9 * w ^ 8 / 8 - w ^ 12 / 8 + 38 * s 2 w / w

/-- `c_N(u) = C_N(u) + 4G_N(u)/u − 2B_N` (p.11). The formula divides by `u`; the page's domain is
`0 < u ≤ 1`. -/
noncomputable def cN (N : ℕ) (u : ℝ) : ℝ := CC N u + 4 * G N u / u - 2 * BB N

end KramerSaglam


