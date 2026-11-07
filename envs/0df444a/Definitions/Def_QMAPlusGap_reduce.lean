-- Prove2me | Definitions.Def_QMAPlusGap_reduce
-- name    : QMAPlusGap_reduce
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:53.972638+00:00
-- url     : https://prove2.me/theorems/afb34a9a-b3ea-4ebb-a538-1fe3ccaae3eb
-- title:
--   Reduction to the first $j$ registers
-- statement:
--   For an operator $X$ on $\mathcal H^{\otimes m}$ and $j\le m$, the **reduction to $j$ registers** is the partial trace over the last $m-j$ registers:
--   $$
--   \langle a|X_j|b\rangle=\sum_{c}\langle a\,c|X|b\,c\rangle ,
--   $$
--   where $a,b$ range over basis strings of the first $j$ registers and $c$ over those of the remaining $m-j$. For $j=0$ this is the scalar $\operatorname{Tr}X$, the paper's convention $X_0=\operatorname{Tr}X$. The companion `reduceOne` regards $X_1$ as an operator $\rho_1$ on $\mathcal H$ itself.
--
--   **Formalization Note** The first $j$ registers are kept. For operators supported on the symmetric subspace every choice of $j$ registers gives the same reduction, which is why the paper says "its reduced state on $j$ registers".
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 11 and p.22; Proposition 9, p.15; Theorem 12, p.25

import Mathlib

set_option autoImplicit false

namespace QMAPlusGap

/-- Glue a basis string `a` of the first `j` registers and a basis string `c` of the remaining `m − j` registers
into a basis string of all `m` registers. -/
def glue {ι : Type} {j m : ℕ} (a : Fin j → ι) (c : Fin (m - j) → ι) : Fin m → ι :=
  fun i => if h : (i : ℕ) < j then a ⟨i, h⟩ else c ⟨(i : ℕ) - j, by have := i.isLt; omega⟩

/-- The **reduction of `X` to `j` registers** (partial trace over registers `j, …, m − 1`), Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…): "its reduced
state on ℓ registers" (Theorem 12, p.25; Lemmas 13, 14, A.1, A.3), "their reductions to N registers" (Proposition
9, p.15), "X_j, Y_j be their reductions to j registers" (Lemma 11, p.20):
`(X_j)_{ab} = Σ_c X_{(a,c),(b,c)}`.

**Formalization Note** The reduction keeps the **first** `j` registers; for operators supported on the symmetric
subspace every choice of `j` registers gives the same operator. `reduce 0 X` is the `1 × 1` matrix `Tr X` on the
one-point index type `Fin 0 → ι` (the paper's convention `X_0 = Tr X`, p.22), and `reduce m X = X`. The
statements always assume `j ≤ m`. -/
def reduce {ι : Type} [Fintype ι] {m : ℕ} (j : ℕ) (X : Matrix (Fin m → ι) (Fin m → ι) ℂ) :
    Matrix (Fin j → ι) (Fin j → ι) ℂ :=
  Matrix.of fun a b => ∑ c : Fin (m - j) → ι, X (glue a c) (glue b c)

/-- The **one-register reduced state `ρ₁`** as an operator on `H = ℂ^ι` itself (Lemmas 13, A.3 and the proof of
Theorem 12): `reduce 1 X` re-indexed from `Fin 1 → ι` to `ι`. -/
def reduceOne {ι : Type} [Fintype ι] {m : ℕ} (X : Matrix (Fin m → ι) (Fin m → ι) ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun a b => reduce 1 X (fun _ => a) (fun _ => b)

end QMAPlusGap


