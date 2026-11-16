-- Prove2me | Definitions.Def_SelectiveDPT_Supplement_matMap
-- name    : SelectiveDPT_Supplement_matMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:28:36.261426+00:00
-- url     : https://prove2.me/theorems/f8cb82f1-3b34-4591-85ff-53a3faecc6da
-- title:
--   Matrix mapping $g_A(F,\tilde F) = FA\tilde F^{\mathsf T}$ and its average success probability
-- statement:
--   A **function matrix** is an $n \times n$ $0/1$ matrix $F$ with exactly one $1$ in every row; it defines $f_F : [n] \to [n]$ by $f_F(i) = \mathsf{SEARCH}_n(F_i)$. For a fixed $A \in \mathbb Z^{n\times n}$ the **matrix mapping problem** is
--   $$g_A(F, \tilde F) = F A \tilde F^{\mathsf T}, \qquad g_A(F,\tilde F)_{i,j} = A_{f_F(i),\, f_{\tilde F}(j)} .$$
--   The input of an algorithm is the $2n^2$ bits of $(F, \tilde F)$, queried one bit at a time. A write-only output tape of pairs $((i,j), v)$ **computes** $g_A(F,\tilde F)$ when every written pair is correct, $v = g_A(F,\tilde F)_{i,j}$, and every coordinate $(i,j) \in [n]^2$ is written. The success probability of a general space-bounded algorithm is averaged over uniformly random function matrices:
--   $$\mathrm{succ}(A) = n^{-2n} \sum_{F, \tilde F} \Pr[\text{the tape computes } g_A(F,\tilde F)] .$$
--
--   This is the problem of the quantum time-space tradeoff of Theorem 4.16.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Definitions 4.13 and 4.14, p.37; §2.3, p.11; Lemma 4.18, p.40

import Mathlib
import Definitions.Def_SelectiveDPT_Supplement_SpaceBoundedAlg

namespace SelectiveDPT.Supplement

/-- The bits of a pair `(F, F̃)` of `n × n` function matrices (arXiv:2609.26678, Definition 4.13,
p.37: "a matrix `F ∈ {0,1}^{n×n}` is a function matrix iff every row has exactly one 1"; it
defines `f_F : [n] → [n]`), given by the functions `f = f_F`, `g = f_F̃`: the query index
`(0, i, j)` reads `F_{ij} = [f(i) = j]` and `(1, i, j)` reads `F̃_{ij} = [g(i) = j]`. These are the
`2n²` input bits of the matrix mapping problem. -/
def fnMatrixPair {n : ℕ} (f g : Fin n → Fin n) : Fin 2 × Fin n × Fin n → ZMod 2 :=
  fun q => if (if q.1 = 0 then f else g) q.2.1 = q.2.2 then 1 else 0

/-- The matrix mapping problem `g_A(F, F̃) = F A F̃ᵀ` (arXiv:2609.26678, Definition 4.14, p.37),
entrywise `g_A(F, F̃)_{i,j} = A_{f_F(i), f_F̃(j)}` (p.37), for the function matrices of `f`, `g`. -/
def matMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (f g : Fin n → Fin n) (i j : Fin n) : ℤ :=
  A (f i) (g j)

/-- An output tape of pairs `((i, j), v)` computes `g_A(F, F̃)` (arXiv:2609.26678, §2.3 and
Theorem 4.16): every written pair is correct, `v = g_A(F, F̃)_{i,j}`, and every coordinate
`(i, j) ∈ [n]²` is written. -/
def ComputesMatMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (f g : Fin n → Fin n)
    (L : List ((Fin n × Fin n) × ℤ)) : Prop :=
  (∀ p ∈ L, p.2 = matMap A f g p.1.1 p.1.2) ∧ ∀ i j, ∃ v, ((i, j), v) ∈ L

/-- The success probability of a general space-bounded algorithm for `g_A`, averaged over
uniformly random function matrices `F, F̃ ∼ F_n` (arXiv:2609.26678, Definition 4.13 and
Lemma 4.18, p.40): `n^{−2n} Σ_{f, g} Pr[the algorithm computes g_A(F_f, F_g)]`. -/
noncomputable def matMapSuccess {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {P : Type*} [Fintype P]
    [DecidableEq P] {T : ℕ} (alg : SpaceBoundedAlg (Fin 2 × Fin n × Fin n) P
      ((Fin n × Fin n) × ℤ) 2 T) : ℝ :=
  (1 / (n : ℝ) ^ (2 * n)) *
    ∑ f : Fin n → Fin n, ∑ g : Fin n → Fin n,
      alg.succProb (fnMatrixPair f g) (ComputesMatMap A f g)

end SelectiveDPT.Supplement


