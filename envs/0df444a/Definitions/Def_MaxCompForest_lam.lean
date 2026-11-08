-- Prove2me | Definitions.Def_MaxCompForest_lam
-- name    : MaxCompForest_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:50.754756+00:00
-- url     : https://prove2.me/theorems/9855cbe5-6c46-49b4-8925-e96110553e2f
-- title:
--   Eigenvalue $\lambda_{j+1}(N_W)$ in ascending order
-- statement:
--   The eigenvalues of the symmetric matrix $N_W$ are listed with multiplicity in ascending order, $\lambda_1\le\dots\le\lambda_n$. This item is
--   $$
--   \mathtt{lam}(G,W,j)=\lambda_{j+1}(N_W),\qquad 0\le j<n .
--   $$
--   The spectral hypothesis of the paper, $\lambda_{q+1}(N_G)\ge\gamma$, is therefore $\gamma\le\mathtt{lam}(G,D,q)$.
--
--   **Formalization Note** Mathlib lists Hermitian eigenvalues in descending order, so the index is reversed. The value at $j\ge n$ is $0$ and is never used.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.2, §2.1 p.7

import Mathlib
import Definitions.Def_MaxCompForest_normLap
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The `(j+1)`-st smallest eigenvalue** of `N_W`, with multiplicity: `lam G W j = λ_{j+1}(N_W)`,
so the hypothesis `λ_{q+1}(N_G) ≥ γ` reads `γ ≤ lam G (deg G) q`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.2: "Order the eigenvalues … as `0 = λ₁ ≤ ⋯ ≤ λₙ`".

**Formalization Note.** Mathlib's `eigenvalues₀` is antitone, so the index is reversed:
`card V − 1 − j`. The value for `j ≥ card V` is `0` and is never used: every statement has `j < card V`.
The sanity file proves that on `K₂` the values are `lam 0 = 0`, `lam 1 = 2`. -/
noncomputable def lam (G : WGraph V E) (W : V → ℝ) (j : ℕ) : ℝ :=
  if h : j < Fintype.card V then
    (normLap_isHermitian G W).eigenvalues₀ ⟨Fintype.card V - 1 - j, by omega⟩
  else 0

end MaxCompForest


