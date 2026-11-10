-- Prove2me | Definitions.Def_QThermalClassical_IsConnectedSeq
-- name    : QThermalClassical_IsConnectedSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:41.226752+00:00
-- url     : https://prove2.me/theorems/6684b078-bbcf-421a-9f92-b7ebab68bda6
-- title:
--   Connected sequences $Q^{(t)}_{K}$ and supports of term lists
-- statement:
--   For a Pauli Hamiltonian with label set $A$ and a site set $K$, a sequence $(b_1,\dots,b_t)$ of terms $b_j\in A$ lies in $Q^{(t)}_K$ (Lemma 8) if
--   $$
--   b_1\cap K\neq\emptyset,\qquad b_j\cap\left(K\cup b_1\cup\cdots\cup b_{j-1}\right)\neq\emptyset\quad (j\ge2),
--   $$
--   where $b\cap K$ abbreviates $\mathrm{supp}(P_b)\cap K$. The paper takes $K=\mathrm{supp}(P_{a^*})$. The support of a list of terms is the union of the supports of its entries (the convention of (78)).
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 8, p.21; Definition 3.1, eq. (78), p.25

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The union of the supports of the words in a list (the support of a product of terms in the
sense of (78): the union of the supports of its factors, not the support of the multiplied-out
operator). -/
def wordsSupport (L : List (PauliWord Q)) : Finset Q :=
  L.toFinset.biUnion pauliSupport

/-- Membership of a sequence `b = (b_1, …, b_t)` of terms in `Q^{(t)}_{K}` (Lemma 8, p.21):
every `b_j` is a term of `H` (`c b_j ≠ 0`), `b_1` meets `K`, and every later `b_j` meets
`K ∪ supp(b_1) ∪ ⋯ ∪ supp(b_{j−1})`. The length of `b` is `t`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 8, p.21.

**Formalization Note.** The paper takes `K = supp(P_{a*})` for a label `a*`; here `K` is any
finite site set, which covers the partially pinned labels of p.26. -/
def IsConnectedSeq (c : PauliWord Q → ℝ) (K : Finset Q) (b : List (PauliWord Q)) : Prop :=
  (∀ P ∈ b, c P ≠ 0) ∧
  ∀ (j : ℕ) (hj : j < b.length), (pauliSupport (b[j]'hj) ∩ (K ∪ wordsSupport (b.take j))).Nonempty

end QThermalClassical


