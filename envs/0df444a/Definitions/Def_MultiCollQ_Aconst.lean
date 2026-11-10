-- Prove2me | Definitions.Def_MultiCollQ_Aconst
-- name    : MultiCollQ_Aconst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:35.710459+00:00
-- url     : https://prove2.me/theorems/b5fd4a38-fab7-4e64-9bcf-bad11273d4aa
-- title:
--   Exponents $\alpha_j,\beta_j$, constants $c_j$, $A_j$ and scales $\lambda_j$ of §3
-- statement:
--   For $j\ge1$ put
--
--   $$
--   \alpha_j=2-2^{1-j},\qquad \beta_j=1-2^{1-j}=\alpha_j-1 .
--   $$
--
--   For a query horizon $1\le T<N$ put $d=N-T$ and $\lambda_j=T^{\alpha_j}/d^{\beta_j}$; for $2\le j\le k$ put $c_j=\sqrt{8(k-j+1)}$. Finally
--
--   $$
--   A_j=\prod_{i=2}^{j}\bigl(8(k-i+1)\bigr)^{2^{i-j-1}},
--   $$
--
--   an empty product being $1$.
--
--   These are the constants of the first-moment recursion (Lemma 3.3, Theorem 3.4, Corollary 3.5) and the exponents of the query scale $\ell^{1/\alpha_r}N^{\beta_r/\alpha_r}$.
--
--   **Formalization Note** All powers with real exponents are `Real.rpow`. In every use the bases are positive ($T\ge1$, $N-T\ge1$, $k-i+1\ge1$).
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), (3.1)–(3.2), p.19; Theorem 3.4, p.25

import Mathlib

namespace MultiCollQ

/-- `α_j = 2 − 2^{1−j}` (Peng, Hou, Dong, manuscript (Oct. 2026), (3.1), p.19). -/
noncomputable def alphaExp (j : ℕ) : ℝ := 2 - (2 : ℝ) ^ (1 - (j : ℝ))

/-- `β_j = 1 − 2^{1−j}` (Peng, Hou, Dong, manuscript (Oct. 2026), (3.1), p.19). -/
noncomputable def betaExp (j : ℕ) : ℝ := 1 - (2 : ℝ) ^ (1 - (j : ℝ))

/-- `c_j = √(8(k − j + 1))` (Peng, Hou, Dong, manuscript (Oct. 2026), (3.2), p.19). Used for
`2 ≤ j ≤ k`, where `k − j + 1 ≥ 1`. -/
noncomputable def cConst (k j : ℕ) : ℝ := Real.sqrt (8 * ((k : ℝ) - j + 1))

/-- `λ_j = T^{α_j} / d^{β_j}` with `d = N − T` (Peng, Hou, Dong, manuscript (Oct. 2026), (3.2),
p.19).

**Formalization Note.** Real powers; every use has `1 ≤ T < N`, so the bases are positive. -/
noncomputable def lambdaScale (N T j : ℕ) : ℝ :=
  (T : ℝ) ^ alphaExp j / ((N : ℝ) - T) ^ betaExp j

/-- `A_j = ∏_{i=2}^{j} (8(k − i + 1))^{2^{i−j−1}}`, an empty product being `1` (Peng, Hou, Dong,
manuscript (Oct. 2026), Theorem 3.4, p.25).

**Formalization Note.** The exponent `2^{i−j−1}` is a real power of `2` (it is negative-exponent for
`i ≤ j`), and the outer power is `Real.rpow`; for `2 ≤ i ≤ j ≤ k` the base `8(k − i + 1)` is
positive. -/
noncomputable def Aconst (k j : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 2 j, (8 * ((k : ℝ) - i + 1)) ^ ((2 : ℝ) ^ ((i : ℝ) - j - 1))

end MultiCollQ


