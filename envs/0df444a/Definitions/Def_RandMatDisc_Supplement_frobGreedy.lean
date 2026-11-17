-- Prove2me | Definitions.Def_RandMatDisc_Supplement_frobGreedy
-- name    : RandMatDisc_Supplement_frobGreedy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:09:49.583987+00:00
-- url     : https://prove2.me/theorems/239c4ad5-683e-4109-8693-a0e3794f5580
-- title:
--   The Frobenius-greedy online signing algorithm (Algorithm 2)
-- statement:
--   Given $A_1,\dots,A_N\in\mathbb R^{d\times d}$, the **Frobenius-greedy algorithm** chooses signs one at a time, each minimizing the Frobenius norm of the running sum. With $\langle X,Y\rangle_F=\sum_{k,\ell}X_{k\ell}Y_{k\ell}$ it sets $S_0=0$, $\sigma_1=1$, $S_1=\sigma_1A_1$, and for $k=2,\dots,N$
--
--   $$\sigma_k=-\operatorname{sign}\langle S_{k-1},A_k\rangle_F\quad(\sigma_k=1\ \text{if}\ \langle S_{k-1},A_k\rangle_F=0),\qquad S_k=S_{k-1}+\sigma_kA_k .$$
--
--   So $\sigma_k=-1$ exactly when $\langle S_{k-1},A_k\rangle_F>0$. It returns $\sigma_1,\dots,\sigma_N$.
--
--   The algorithm is online: $\sigma_k$ depends only on $A_1,\dots,A_k$. Theorems 2.6 and 2.7 determine its exact limiting discrepancy on GOE inputs.
--
--   **Formalization Note** Indices are 0-based. The first sign $\sigma_1=1$ comes from applying the tie rule to $S_0=0$. Signs are the reals $\pm1$, and inputs are arrays `Fin d → Fin d → ℝ`.
-- source:
--   Kızıldağ, Li, Stable and Online Algorithms for Random Matrix Discrepancy, arXiv:2610.01591 (preprint; held file sha256 889af7fc2595be5c653c6b477e70fa5898c7b743d8720cda44ca99761d629a13), §2.2, p.12 (PDF p.14), Algorithm 2

import Mathlib

namespace RandMatDisc.Supplement

/-- The Frobenius inner product `⟨X, Y⟩_F = Σ_{k,ℓ} X_{kℓ} Y_{kℓ}` of two `d × d` arrays. -/
def frobInner {d : ℕ} (X Y : Fin d → Fin d → ℝ) : ℝ := ∑ k, ∑ l, X k l * Y k l

/-- The sign rule of Algorithm 2, step 3: `σ_k = −sign⟨S_{k−1}, A_k⟩_F`, and `σ_k = 1` if
`⟨S_{k−1}, A_k⟩_F = 0`. So `σ_k = −1` exactly when the inner product is positive. -/
noncomputable def fgSign {d : ℕ} (S B : Fin d → Fin d → ℝ) : ℝ :=
  if 0 < frobInner S B then -1 else 1

/-- The `k`-th input matrix, extended by `0` beyond `N` (only `k < N` is ever read). -/
def fgInput {d N : ℕ} (A : Fin N → Fin d → Fin d → ℝ) (k : ℕ) : Fin d → Fin d → ℝ :=
  if h : k < N then A ⟨k, h⟩ else 0

/-- The partial sums `S_k = Σ_{j ≤ k} σ_j A_j` of Algorithm 2 (with `S₀ = 0`, 0-indexed
inputs: `fgSum A k` is the sum over the first `k` matrices). -/
noncomputable def fgSum {d N : ℕ} (A : Fin N → Fin d → Fin d → ℝ) : ℕ → Fin d → Fin d → ℝ
  | 0 => 0
  | k + 1 => fgSum A k + fgSign (fgSum A k) (fgInput A k) • fgInput A k

/-- **Algorithm 2 (Frobenius-greedy algorithm)**, p.12 (PDF p.14) of Kızıldağ, Li, *Stable and
Online Algorithms for Random Matrix Discrepancy*, arXiv:2610.01591 (held file sha256 889af7fc…):

```
Require: A₁, …, A_N ∈ ℝ^{d×d}
1: Set S₀ ← 0, σ₁ = 1, and S₁ = σ₁A₁.
2: for k = 2, 3, …, N do
3:    Set σ_k = −sign⟨S_{k−1}, A_k⟩_F. If ⟨S_{k−1}, A_k⟩_F = 0, declare σ_k = 1.
4:    Update S_k ← S_{k−1} + σ_kA_k
5: end for
6: return σ₁, …, σ_N.
```

`frobGreedy A i` is the sign of the `(i+1)`-st matrix (0-indexed `i : Fin N`).

**Formalization Note.** Indices are 0-based. Step 1's `σ₁ = 1` is the sign rule applied to
`S₀ = 0` (inner product `0`, so the tie rule gives `+1`). Signs are reals `±1`. The algorithm is
deterministic. -/
noncomputable def frobGreedy {d N : ℕ} (A : Fin N → Fin d → Fin d → ℝ) : Fin N → ℝ :=
  fun i => fgSign (fgSum A i) (A i)

end RandMatDisc.Supplement


