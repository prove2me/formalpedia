-- Prove2me | Definitions.Def_MonDepMW_IsDampingSequence
-- name    : MonDepMW_IsDampingSequence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:02.396863+00:00
-- url     : https://prove2.me/theorems/eb88e2f8-4160-4c95-add3-72962f4b9f8d
-- title:
--   The sequence of vertex sets of Theorem 4.3
-- statement:
--   For $q\geqslant2$ and a value $k$, this predicate says that $\emptyset=B_m\subseteq\dots\subseteq B_0=V(G)$ with $m\leqslant1+\log_qn$, and that with $\mathcal P_i=\mathcal T_1(G,B_i)$, for every $i\in[m]$ and vertex $u$, $\mathrm{Ball}^r_{\mathcal P_i}[u]$ intersects at most
--   $$k'=q^r(\log_qn+1)\,k$$
--   parts of $\mathcal P_{i-1}$; and that $\mathcal P_0\sqsubseteq\dots\sqsubseteq\mathcal P_m$ is a partition sequence of radius-$r$ width at most $k'$.
--
--   It is the conclusion of Theorem 4.3, stated once for its existence and algorithmic clauses.
--
--   **Formalization Note** Widths are integers, so the sequence's width is compared with $\lfloor k'\rfloor$. At $n=0$, $\log_q n$ is $0$ in Lean.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §4, p.16, Theorem 4.3

import Mathlib
import Definitions.Def_MonDepMW_PartitionSeq

set_option autoImplicit false

namespace MonDepMW

/-- **The sequence of Theorem 4.3.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.16: "a sequence of vertex subsets ∅ = Bm ⊆ Bm−1 ⊆ . . . ⊆ B1 ⊆ B0 = V (G) with
m ⩽ 1 + log_q n satisfying the following condition. For every i ∈ [m] and u ∈ V (G), Ball^r_{𝒫i}[u] intersects at most
k′(n) := q^r · (log_q n + 1) · k(n) parts of 𝒫i−1, where 𝒫i := 𝒯1(G, Bi). In particular, 𝒫0 ⊑ 𝒫1 ⊑ . . . ⊑ 𝒫m is a
partition sequence for G of radius-r width at most k′(n)." Here `k` is the value `k(n)`.

**Formalization Note.** `log_q n` is `Real.logb q n` with `q ≥ 2` in every use; at `n = 0` it is `0`. The width of a
sequence is an integer, so "at most `k′(n)`" for the sequence is `⌊k′(n)⌋`. -/
structure IsDampingSequence {n : ℕ} (G : SimpleGraph (Fin n)) (q r k m : ℕ) (B : ℕ → Finset (Fin n)) : Prop where
  m_le : (m : ℝ) ≤ 1 + Real.logb q n
  B_zero : B 0 = Finset.univ
  B_last : B m = ∅
  chain : ∀ i, i < m → B (i + 1) ⊆ B i
  hits : ∀ i, 1 ≤ i → i ≤ m → ∀ u,
    (partsHit (oneType G (B (i - 1))) (flipBall G (oneType G (B i)) r u) : ℝ) ≤
      (q : ℝ) ^ r * (Real.logb q n + 1) * (k : ℝ)
  valid : (PartitionSeq.ofSets G m B).IsValid
  width_le : (PartitionSeq.ofSets G m B).WidthLE G r
    ⌊(q : ℝ) ^ r * (Real.logb q n + 1) * (k : ℝ)⌋₊

end MonDepMW


