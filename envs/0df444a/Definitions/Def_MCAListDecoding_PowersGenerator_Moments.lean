-- Prove2me | Definitions.Def_MCAListDecoding_PowersGenerator_Moments
-- name    : MCAListDecoding_PowersGenerator_Moments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:17:24.21106+00:00
-- url     : https://prove2.me/theorems/40871ed8-0d47-4540-a654-2b15b6a5b514
-- title:
--   Agreement moments of a family of sets
-- statement:
--   Let $S$ be a finite index set of size $M\ge1$ and $A(x)\subseteq[n]$ for $x\in S$. For $i\in[n]$ put $A_i=|\{x\in S : i\in A(x)\}|$. The **$j$-th agreement moment** is
--   $$\mu_j=\frac1n\sum_{i\in[n]}\frac{(A_i)_j}{(M)_j},\qquad (y)_j=y(y-1)\cdots(y-j+1),$$
--   with $(A_i)_j=0$ when $A_i<j$. The real falling factorial $(y)_j=\prod_{m<j}(y-m)$ is used for $y=M(1-\gamma)$ in Lemma 5.2.
--
--   **Formalization Note.** $S$ is a `Finset` of an arbitrary type, $A$ a map to `Finset (Fin n)`; $(A_i)_j$ and $(M)_j$ are `Nat.descFactorial`, which is $0$ below $j$ as in the paper. The definition is total for every $j$; the paper uses it for $1\le j\le M$, where $(M)_j>0$.
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), §5.1, Definition 5.1, p. 32

import Mathlib

/-!
# Agreement moments of a family of sets

Manzur, *Mutual Correlated Agreement and List-Decoding: Improvements and Separations*,
STOC 2027 submission (manuscript of 2026-11-03), §5.1, Definition 5.1 (p. 32).

A finite index set `S` (a `Finset` of an arbitrary type `ι`) of size `M`, and a set
`A(x) ⊆ [n]` for each index (`A : ι → Finset (Fin n)`).

**Formalization Note.** `(y)_j = y(y-1)⋯(y-j+1)` on natural numbers is `Nat.descFactorial y j`,
which is `0` when `y < j` (the paper's convention). The real falling factorial
`(M(1-γ))_j` of Lemma 5.2 is `realFalling`, the product `∏_{m<j} (y - m)`.
-/

namespace MCAListDecoding.PowersGenerator

/-- `A_i = |{x ∈ S : i ∈ A(x)}|` (§5.1, p. 32). -/
noncomputable def coordCount {ι : Type*} {n : ℕ} (S : Finset ι) (A : ι → Finset (Fin n))
    (i : Fin n) : ℕ := by
  classical
  exact (S.filter fun x => i ∈ A x).card

/-- The `j`-th agreement moment `μ_j = (1/n) ∑_{i ∈ [n]} (A_i)_j / (M)_j` with `M = |S|` and
falling factorials (Definition 5.1, p. 32). -/
noncomputable def agreementMoment {ι : Type*} {n : ℕ} (S : Finset ι) (A : ι → Finset (Fin n))
    (j : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n,
    ((coordCount S A i).descFactorial j : ℝ) / ((S.card.descFactorial j : ℕ) : ℝ)

/-- The real falling factorial `(y)_j = y (y - 1) ⋯ (y - j + 1)`. -/
def realFalling (y : ℝ) (j : ℕ) : ℝ :=
  ∏ m ∈ Finset.range j, (y - (m : ℝ))

end MCAListDecoding.PowersGenerator


