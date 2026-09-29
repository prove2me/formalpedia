-- Prove2me | Definitions.Def_HighDimStat_SparseLinear_PairwiseIncoherence
-- name    : HighDimStat_SparseLinear_PairwiseIncoherence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:07:25.658058+00:00
-- url     : https://prove2.me/theorems/eb3c642f-80ab-48c8-9383-19532a2d12fe
-- title:
--   The pairwise incoherence parameter of a design matrix
-- statement:
--   This is the **pairwise incoherence** parameter $\delta_{PW}(X)$ of Eq. (7.12), measuring
--   how far the Gram matrix of the (rescaled) columns of $X$ is from the identity. Proposition
--   7.9 shows that a small pairwise incoherence certifies the restricted nullspace property.
--
--   For $X \in \mathbb R^{n\times d}$ with columns $X_1,\dots,X_d \in \mathbb R^n$,
--
--   $$
--   \delta_{PW}(X) \;:=\; \max_{j,k=1,\dots,d} \left| \frac{\langle X_j, X_k\rangle}{n} -
--   \mathbb 1[j=k] \right|.
--   $$
--
--   **Formalization Note** Realized as `⨆` (real supremum) over the finite index type `Fin d
--   × Fin d`, matching the book's `max` for $d>0$; at $d=0$ it is Mathlib's junk value `0`,
--   harmless since no columns exist to compare. The inner product $\langle X_j, X_k \rangle$
--   is written directly as $\sum_i X_{ij} X_{ik}$.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 203 (PDF p. 223), Eq. (7.12)

import Mathlib

namespace HighDimStat.SparseLinear

/-- The pairwise incoherence parameter `δ_PW(X) := max_{j,k} |⟨Xⱼ,Xₖ⟩/n − 𝟙[j=k]|` of
Wainwright, *High-Dimensional Statistics* (2019), Eq. (7.12), p. 203, where `Xⱼ` denotes the
`j`-th column of `X`. Realized as `⨆` over the finite index type `Fin d × Fin d`; at `d = 0`
this is Mathlib's junk value `0`. -/
noncomputable def pairwiseIncoherence {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) : ℝ :=
  ⨆ jk : Fin d × Fin d,
    |(∑ i, X i jk.1 * X i jk.2) / (n : ℝ) - (if jk.1 = jk.2 then (1 : ℝ) else 0)|

end HighDimStat.SparseLinear


