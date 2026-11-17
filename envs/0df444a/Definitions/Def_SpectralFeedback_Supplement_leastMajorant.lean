-- Prove2me | Definitions.Def_SpectralFeedback_Supplement_leastMajorant
-- name    : SpectralFeedback_Supplement_leastMajorant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:54:34.109869+00:00
-- url     : https://prove2.me/theorems/d7b5fab6-6f14-4b26-a7b2-8a2ee7fcbd94
-- title:
--   The least rank-$r'$ majorant $q=(\lambda_1,\dots,\lambda_j,\tau,\dots,\tau,0,\dots,0)$
-- statement:
--   Let $\lambda_1\ge\dots\ge\lambda_n>0$ be a spectrum and $1\le r'\le n$. Choose the smallest $j\in\{0,\dots,r'-1\}$ with
--
--   $$
--   \lambda_{j+1}\le\tau,\qquad \tau=\frac{\sum_{i>j}\lambda_i}{r'-j},
--   $$
--
--   and put $q=q^{(r')}(\lambda)=(\lambda_1,\dots,\lambda_j,\tau,\dots,\tau,0,\dots,0)\in\mathbb R^n$, with $r'-j$ entries equal to $\tau$. For a probability vector $\lambda$ this is the least rank-$r'$ probability vector majorizing $\lambda$. The unlimited-message value is $G_{\infty,r}(\rho)=\chi(q)$, and Theorems C.4 and E.1 characterize when finitely many symbols attain it.
--
--   **Formalization Note** Three definitions: `wfLevel` (the level $\tau_j$), `wfIndex` (the head size $j$) and `leastMajorant` ($q$). Indices are 0-based: `lam i` is $\lambda_{i+1}$, so $\sum_{i>j}$ becomes the sum over $i\in[j,n)$, and entry $i$ of $q$ is `lam i` for $i<j$, $\tau$ for $j\le i<r'$ and $0$ after that. For a nonnegative decreasing list with $1\le r'\le n$ the index $j=r'-1$ always qualifies. The fallback value $j=0$ is used only when no index qualifies, which no statement of the mission uses.
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), §C.4, p.29 (PDF p.31); §E.1, p.75 (PDF p.77)

import Mathlib

namespace SpectralFeedback

namespace Supplement

/-- **The water level `τ_j`** of the least rank-`r′` majorant (Qi, *Spectral Structure and Exact
Arithmetic of Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), §C.4, p.29
(PDF p.31); §E.1, p.75 (PDF p.77)): `τ = ∑_{i>j} λ_i / (r′ − j)`, the sum running over
`j < i ≤ n`.

**Formalization Note** 0-based: `lam i` is the paper's `λ_{i+1}`, so the sum is over
`i ∈ [j, n)`. Used only with `j < r′`, where the denominator is positive. -/
noncomputable def wfLevel (lam : ℕ → ℝ) (n r' j : ℕ) : ℝ :=
  (∑ i ∈ Finset.Ico j n, lam i) / ((r' : ℝ) - (j : ℝ))

open Classical in
/-- **The head size `j`** of the least rank-`r′` majorant (Qi, manuscript (Nov. 2026), §C.4, p.29
(PDF p.31); §E.1, p.75): the smallest `j ∈ {0, …, r′ − 1}` with `λ_{j+1} ≤ τ_j`.

**Formalization Note** 0-based (`lam j` is `λ_{j+1}`). For a nonnegative decreasing list with
`1 ≤ r′ ≤ n` the index `j = r′ − 1` always qualifies, so the minimum exists; the fallback value `0`
is used only when no index qualifies (e.g. `r′ = 0`). -/
noncomputable def wfIndex (lam : ℕ → ℝ) (n r' : ℕ) : ℕ :=
  if h : ∃ j, j < r' ∧ lam j ≤ wfLevel lam n r' j then Nat.find h else 0

/-- **The least rank-`r′` probability vector majorizing `λ`** (Qi, *Spectral Structure and Exact
Arithmetic of Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), §C.4, p.29
(PDF p.31); §E.1, p.75 (PDF p.77)): with `j = wfIndex` and `τ = τ_j`,
`q = (λ_1, …, λ_j, τ, …, τ, 0, …, 0) ∈ ℝ^n`, with `r′ − j` entries equal to `τ`.

**Formalization Note** 0-based: entry `i` is `lam i` for `i < j`, `τ` for `j ≤ i < r′`, and `0`
for `r′ ≤ i < n`. -/
noncomputable def leastMajorant (lam : ℕ → ℝ) (n r' : ℕ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < wfIndex lam n r' then lam i
    else if (i : ℕ) < r' then wfLevel lam n r' (wfIndex lam n r') else 0

end Supplement

end SpectralFeedback


