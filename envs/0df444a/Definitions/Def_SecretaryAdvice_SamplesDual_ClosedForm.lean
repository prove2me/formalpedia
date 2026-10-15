-- Prove2me | Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm
-- name    : SecretaryAdvice_SamplesDual_ClosedForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:28.668063+00:00
-- url     : https://prove2.me/theorems/3d599208-0976-4706-bc1c-0287483bcbe1
-- title:
--   Theorem 17 and its proof, pp. 17–18 — the closed-form expressions: the formula of Theorem 17, T(i,s′), and the key-identity sum
-- statement:
--   Let $n,k\ge 0$, a round $1\le i\le n$ and a signal $0\le s\le k$. Throughout, $\prod_{t=a}^{b}x_t=1$ when $b<a$ (the convention of p. 17). For $i<n$ the expression inside the maximum of Theorem 17 is
--
--   $$F(i,s)=\frac{1}{k+1}\prod_{t=1}^{i-1}\frac{s+t}{k+t+1}\left(\prod_{t=i}^{n-1}\frac{s+t}{k+t+1}-\frac{\sum_{j=1}^{n-i}\binom{n-i}{j}\frac1j\prod_{\ell=1}^{j}(k-s+\ell)\prod_{\ell=1}^{n-i-j}(s+i-1+\ell)}{\prod_{t=i}^{n-1}(k+t+1)}\right).$$
--
--   The **explicit formula** of Theorem 17 is $a(n,s)=\frac{1}{k+1}\prod_{t=1}^{n-1}\frac{s+t}{k+t+1}$ for $i=n$ and $\max\{0,F(i,s)\}$ for $i<n$; the **un-clipped formula** is $a(n,s)$ for $i=n$ and $F(i,s)$ for $i<n$.
--
--   The auxiliary quantity of the proof (p. 17, first displayed form) is
--
--   $$T(i,s')=(n-i)\prod_{t=i+1}^{n-1}(s'+t)-\sum_{z=i+1}^{n-1}\sum_{j=1}^{n-z}\binom{n-z}{j}\frac1j\prod_{\ell=1}^{j}(k-s'+\ell)\prod_{t=i+1}^{n-j-1}(s'+t),$$
--
--   and the right-hand side of the key identity (p. 18) is
--
--   $$R(i,s)=\sum_{j=1}^{n-i}\binom{n-i}{j}\frac1j\prod_{\ell=1}^{j}(k-s+\ell)\prod_{t=i}^{n-j-1}(s+t).$$
--
--   These are the expressions the milestones and the goal of the mission compare against the dual recursion.
--
--   **Formalization Note** All naturals are cast to $\mathbb R$ before the subtraction $k-s$; the natural-number differences $n-i$, $n-z$, $n-i-j$, $n-j-1$ appear only as summation bounds and binomial arguments, where the summation ranges keep them non-truncated for $1\le i<n$. $F$ is named `innerFormula`, the explicit formula `explicitFormula`, the un-clipped one `unclippedFormula`, $T$ is `T`, $R$ is `keyRHS`.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 17, Theorem 17 and the definition of T(i, s′) in its proof; p. 18, the key identity

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_Coefficients

namespace SecretaryAdvice.SamplesDual

/-!
The closed-form expressions of Theorem 17 and of its proof, pp. 17–18 of Dütting et al.,
*Secretaries with Advice* (arXiv:2011.06726v1). All products `∏_{t=a}^{b}` are over
`Finset.Icc a b`, which is empty (product `1`) when `b < a`, the paper's convention (p. 17).
Natural-number arguments `n, k, i, s` are cast to `ℝ` before any subtraction `k − s`.
-/

/-- The expression inside `max {0, ·}` in Theorem 17 (p. 17), for `i < n`:
`1/(k+1) · ∏_{t=1}^{i−1} (s+t)/(k+t+1) · ( ∏_{t=i}^{n−1} (s+t)/(k+t+1)
  − [Σ_{j=1}^{n−i} C(n−i,j) · (1/j) · ∏_{ℓ=1}^{j} (k−s+ℓ) · ∏_{ℓ=1}^{n−i−j} (s+i−1+ℓ)]
    / ∏_{t=i}^{n−1} (k+t+1) )`. -/
noncomputable def innerFormula (n k i s : ℕ) : ℝ :=
  1 / ((k : ℝ) + 1) * (∏ t ∈ Finset.Icc 1 (i - 1), ((s : ℝ) + t) / ((k : ℝ) + t + 1)) *
    ((∏ t ∈ Finset.Icc i (n - 1), ((s : ℝ) + t) / ((k : ℝ) + t + 1)) -
      (∑ j ∈ Finset.Icc 1 (n - i),
          ((n - i).choose j : ℝ) * (1 / (j : ℝ)) *
            (∏ ℓ ∈ Finset.Icc 1 j, ((k : ℝ) - s + ℓ)) *
            (∏ ℓ ∈ Finset.Icc 1 (n - i - j), ((s : ℝ) + i - 1 + ℓ))) /
        (∏ t ∈ Finset.Icc i (n - 1), ((k : ℝ) + t + 1)))

/-- The right-hand side of Theorem 17: `u(n,s) = a(n,s) = 1/(k+1)·∏_{t=1}^{n−1}(s+t)/(k+t+1)`
for `i = n`, and `max {0, innerFormula}` for `i < n`. -/
noncomputable def explicitFormula (n k i s : ℕ) : ℝ :=
  if i = n then coeffA n k s else max 0 (innerFormula n k i s)

/-- The claim of the proof of Theorem 17 with `max {0, ·}` ignored:
`a(n,s)` for `i = n`, `innerFormula` for `i < n`. -/
noncomputable def unclippedFormula (n k i s : ℕ) : ℝ :=
  if i = n then coeffA n k s else innerFormula n k i s

/-- `T(i,s')`, proof of Theorem 17, p. 17, first displayed form:
`T(i,s') = (n−i) ∏_{t=i+1}^{n−1} (s'+t)
  − Σ_{z=i+1}^{n−1} Σ_{j=1}^{n−z} C(n−z,j) · (1/j) · ∏_{ℓ=1}^{j} (k−s'+ℓ) · ∏_{t=i+1}^{n−j−1} (s'+t)`. -/
noncomputable def T (n k i s' : ℕ) : ℝ :=
  ((n : ℝ) - i) * (∏ t ∈ Finset.Icc (i + 1) (n - 1), ((s' : ℝ) + t)) -
    ∑ z ∈ Finset.Icc (i + 1) (n - 1), ∑ j ∈ Finset.Icc 1 (n - z),
      ((n - z).choose j : ℝ) * (1 / (j : ℝ)) *
        (∏ ℓ ∈ Finset.Icc 1 j, ((k : ℝ) - s' + ℓ)) *
        (∏ t ∈ Finset.Icc (i + 1) (n - j - 1), ((s' : ℝ) + t))

/-- The right-hand side of the key identity, proof of Theorem 17, p. 18:
`Σ_{j=1}^{n−i} C(n−i,j) · (1/j) · ∏_{ℓ=1}^{j} (k−s+ℓ) · ∏_{t=i}^{n−j−1} (s+t)`. -/
noncomputable def keyRHS (n k i s : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (n - i),
    ((n - i).choose j : ℝ) * (1 / (j : ℝ)) *
      (∏ ℓ ∈ Finset.Icc 1 j, ((k : ℝ) - s + ℓ)) *
      (∏ t ∈ Finset.Icc i (n - j - 1), ((s : ℝ) + t))

end SecretaryAdvice.SamplesDual


