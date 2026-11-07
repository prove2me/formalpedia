-- Prove2me | Definitions.Def_PrivOptTest_Trie
-- name    : PrivOptTest_Trie
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:54.748518+00:00
-- url     : https://prove2.me/theorems/d998f7be-7263-45fc-b309-70aab49479b0
-- title:
--   Blocks, the lifting $\psi_A,\psi_B$, the binary trie counts, the escaped-points function $F$ and the final statistics of Algorithm 2
-- statement:
--   Records are $b$-bit strings read as integers. For a dataset $S$ of size $n$, $S^{\downarrow}_k$ and $S^{\uparrow}_k$ are the multisets of its $k$ smallest and $k$ largest elements (pp.15–16). The liftings of Lemma 3.5 are $\psi_A(x)=x\|1=2x+1$ and $\psi_B(x)=x\|0=2x$.
--
--   A node $p\in\{0,1\}^\ell$ of the binary trie (Definition 3.7) is an integer below $2^\ell$, with $\mathrm{prefix}_\ell(x)=\lfloor x/2^{b-\ell}\rfloor$; $|A^\ell_p|$ is the number of records with prefix $p$, and the children of $p$ are $p0=2p$, $p1=2p+1$. The **escaped-points function** of Lemma 3.10 is $F(\ell)=n-\max_{p\in\{0,1\}^\ell}\min\{|A^\ell_p|,|B^\ell_p|\}$.
--
--   The **promise** is that every Alice record is below every Bob record (Match order) or every one is above (Far order). The **unnoised statistics** of Algorithm 2 are
--   $$\max_{p\in\{0,1\}^L}\{6|A^L_p|+|A^{L+1}_{p0}|\}-\max_{p\in\{0,1\}^L}\{6|A^L_p|+|A^{L+1}_{p1}|\}$$
--   (lines 14–15) and
--   $$\max_{p\in\{0,1\}^H}\Big\{6|A^H_p|+\sum_{q<p}|A^H_q|\Big\}-\max_{p\in\{0,1\}^H}\Big\{6|A^H_p|+\sum_{q>p}|A^H_q|\Big\}$$
--   (lines 17–18), each computed on one party's own records. Two record lists **differ by one replacement** if, as multisets, one is the other with one element exchanged.
--
--   **Formalization Note** Blocks are sorted lists; the lexicographic order of nodes is the integer order.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), §3.2.1, pp.15–16; Lemma 3.5, p.16; Definition 3.7, Lemmas 3.8, 3.10, p.17; Algorithm 2, p.20

import Mathlib

namespace PrivOptTest

/-- The records sorted increasingly: `s_(1) ≤ ⋯ ≤ s_(n)` (§3.2.1, pp.15–16 of arXiv:2611.03599,
manuscript sha256 4ac94dcf…). -/
def sortedRecs {n : ℕ} (S : Fin n → ℕ) : List ℕ :=
  (List.ofFn S).insertionSort (· ≤ ·)

/-- The multiset `S↓_k` of the `k` smallest elements (pp.15–16), as a sorted list. -/
def blockDown {n : ℕ} (k : ℕ) (S : Fin n → ℕ) : List ℕ :=
  (sortedRecs S).take k

/-- The multiset `S↑_k` of the `k` largest elements (pp.15–16), as a sorted list. -/
def blockUp {n : ℕ} (k : ℕ) (S : Fin n → ℕ) : List ℕ :=
  (sortedRecs S).drop (n - k)

/-- `ψ_A(x) = x∥1`, Lemma 3.5, p.16: reading strings as integers, `2x + 1`. -/
def psiA (x : ℕ) : ℕ := 2 * x + 1

/-- `ψ_B(x) = x∥0`, Lemma 3.5, p.16: reading strings as integers, `2x`. -/
def psiB (x : ℕ) : ℕ := 2 * x

/-- `prefix_ℓ(x)` of a `b`-bit string read as an integer (Definition 3.7, p.17). A depth-`ℓ` node
`p ∈ {0,1}^ℓ` is an integer below `2^ℓ`, with children `p0 = 2p`, `p1 = 2p + 1` and lexicographic
order the integer order. -/
def prefixOf (b ℓ x : ℕ) : ℕ := x / 2 ^ (b - ℓ)

/-- The node count `|A^ℓ_p|` of Definition 3.7, p.17. -/
def nodeCount (b ℓ : ℕ) (recs : List ℕ) (p : ℕ) : ℕ :=
  recs.countP fun x => prefixOf b ℓ x = p

/-- `max_{p∈{0,1}^ℓ} min{|A^ℓ_p|, |B^ℓ_p|}`, Lemma 3.10, p.17. -/
def commonMax (b ℓ : ℕ) (A B : List ℕ) : ℕ :=
  (Finset.range (2 ^ ℓ)).sup fun p => min (nodeCount b ℓ A p) (nodeCount b ℓ B p)

/-- **The escaped-points function** `F(ℓ) = n − max_{p∈{0,1}^ℓ} min{|A^ℓ_p|, |B^ℓ_p|}`, Lemma 3.10, p.17.
The subtraction is never truncated when `A` has `n` elements. -/
def escaped (n b ℓ : ℕ) (A B : List ℕ) : ℕ :=
  n - commonMax b ℓ A B

/-- The Match order of the blocks: `max S↑_{A,k} < min S↓_{B,k}`, Lemma 3.5 (1), p.16. -/
def MatchOrder (A B : List ℕ) : Prop := ∀ a ∈ A, ∀ b ∈ B, a < b

/-- The Far order of the blocks: `min S↑_{A,k} > max S↓_{B,k}`, Lemma 3.5 (2), p.16. -/
def FarOrder (A B : List ℕ) : Prop := ∀ a ∈ A, ∀ b ∈ B, b < a

/-- "The promise" of Lemmas 3.8 and 3.10, p.17, as the proof of Lemma 3.8 opens: either of the two
strict orders of Lemma 3.5 and Remark 3.6. -/
def Promise (A B : List ℕ) : Prop := MatchOrder A B ∨ FarOrder A B

/-- `max_{p∈{0,1}^L} {6|A^L_p| + |A^{L+1}_{pj}|}`, the maximizations of Algorithm 2, lines 14–15, p.20
(`j = 0` or `j = 1`). -/
def jumpMax (b L j : ℕ) (recs : List ℕ) : ℕ :=
  (Finset.range (2 ^ L)).sup fun p =>
    6 * nodeCount b L recs p + nodeCount b (L + 1) recs (2 * p + j)

/-- The unnoised statistic of Algorithm 2, lines 14–15, p.20 (large-jump case, `H = L + 1`). -/
def statJump (b L : ℕ) (recs : List ℕ) : ℤ :=
  (jumpMax b L 0 recs : ℤ) - jumpMax b L 1 recs

/-- `max_{p∈{0,1}^H} {6|A^H_p| + Σ_{q<p} |A^H_q|}`, Algorithm 2, lines 17–18, p.20. -/
def cumLeftMax (b H : ℕ) (recs : List ℕ) : ℕ :=
  (Finset.range (2 ^ H)).sup fun p =>
    6 * nodeCount b H recs p + ∑ q ∈ Finset.range p, nodeCount b H recs q

/-- `max_{p∈{0,1}^H} {6|A^H_p| + Σ_{q>p} |A^H_q|}`, Algorithm 2, lines 17–18, p.20. -/
def cumRightMax (b H : ℕ) (recs : List ℕ) : ℕ :=
  (Finset.range (2 ^ H)).sup fun p =>
    6 * nodeCount b H recs p + ∑ q ∈ Finset.Ioo p (2 ^ H), nodeCount b H recs q

/-- The unnoised statistic of Algorithm 2, lines 17–18, p.20 (cumulative-escape case). -/
def statCum (b H : ℕ) (recs : List ℕ) : ℤ :=
  (cumLeftMax b H recs : ℤ) - cumRightMax b H recs

/-- Two lists of records **differ by at most one replacement** (Remark 3.6, p.16; §2.1, p.13): as
multisets, `l'` is `l` with one element `x` exchanged for one element `y` (possibly `x = y`). Written
`x :: l' ~ y :: l`, so that it also covers empty lists. -/
def OneReplaced (l l' : List ℕ) : Prop :=
  ∃ x y : ℕ, (x :: l').Perm (y :: l)

end PrivOptTest


