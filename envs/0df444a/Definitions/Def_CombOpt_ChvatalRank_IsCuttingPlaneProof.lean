-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_IsCuttingPlaneProof
-- name    : CombOpt_ChvatalRank_IsCuttingPlaneProof
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:16.702863+00:00
-- url     : https://prove2.me/theorems/7c18c24b-2e9a-4a79-9bab-f5c2cdef45d4
-- title:
--   Cutting-plane proof of $w^Tx\le t$ from $Ax\le b$
-- statement:
--   A **cutting-plane proof** of $w^Tx\le t$ from the system $a_i^Tx\le b_i$ $(i=1,\dots,m)$ is a sequence of inequalities $a_{m+k}^Tx\le b_{m+k}$ $(k=1,\dots,M)$ together with nonnegative numbers $y_{kj}$ such that, for each $k$, the inequality $a_{m+k}^Tx\le b_{m+k}$ is derived from the system $a_i^Tx\le b_i$ $(i=1,\dots,m+k-1)$ using the numbers $y_{kj}$, and such that the last inequality in the sequence is $w^Tx\le t$.
--
--   Each inequality may thus use the original rows and all earlier cuts. Such a proof shows that $w^Tx\le t$ holds for all integral solutions of the system.
--
--   **Formalization Note** Rows are numbered from $0$ and the proof has $M+1$ derived inequalities, numbered $m,\dots,m+M$: the sequence is nonempty because it has a last inequality. Entries of the sequences past position $m+M$ are unconstrained and play no role.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.7, p. 230 (PDF 238)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsDerivedCut

open Matrix

namespace CombOpt.ChvatalRank

/-- **Cutting-plane proof.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.7, p. 230 (PDF 238): "a cutting-plane proof of an inequality
wᵀx ≤ t from the system (6.20) is a sequence of inequalities a_{m+k}ᵀx ≤ b_{m+k} (k = 1, …, M)
together with nonnegative numbers y_{kj} (1 ≤ k ≤ M, 1 ≤ j ≤ m + k − 1) such that for each k = 1, …, M,
the inequality a_{m+k}ᵀx ≤ b_{m+k} is derived from the system aᵢᵀx ≤ bᵢ (i = 1, …, m + k − 1) using
the numbers y_{kj}, j = 1, …, m + k − 1, and such that the last inequality in the sequence is
wᵀx ≤ t."

**Formalization Note.** Rows are numbered from `0`: `seqA i`, `seqB i` for `i < m` are the rows of
`Ax ≤ b`, and the `M + 1` derived inequalities are `seqA (m + k) ᵀ x ≤ seqB (m + k)`, `k = 0, …, M`.
Each is derived from the `m + k` rows before it. The book's `M` is our `M + 1`: the sequence is
nonempty because it has a last inequality. Values of `seqA`, `seqB`, `y` past the index `m + M` are
unconstrained and irrelevant. -/
def IsCuttingPlaneProof {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (w : Fin n → ℝ) (t : ℝ) : Prop :=
  ∃ (M : ℕ) (seqA : ℕ → Fin n → ℝ) (seqB : ℕ → ℝ) (y : (k : ℕ) → Fin (m + k) → ℝ),
    (∀ i : Fin m, seqA i = A i ∧ seqB i = b i) ∧
    (∀ k ≤ M, IsDerivedCut (fun j : Fin (m + k) => seqA j) (fun j : Fin (m + k) => seqB j) (y k)
      (seqA (m + k)) (seqB (m + k))) ∧
    seqA (m + M) = w ∧ seqB (m + M) = t

end CombOpt.ChvatalRank


