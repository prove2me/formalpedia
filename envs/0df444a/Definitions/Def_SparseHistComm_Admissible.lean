-- Prove2me | Definitions.Def_SparseHistComm_Admissible
-- name    : SparseHistComm_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:47.100899+00:00
-- url     : https://prove2.me/theorems/02bbec83-c459-4b80-b5c5-603a4db20119
-- title:
--   Admissible input profile: every $x_i$ is $k$-sparse
-- statement:
--   Each of $n$ users holds a binary vector $x_i \in \{0,1\}^d$. An input profile $(x_1,\dots,x_n)$ is **admissible** for the sparsity level $k$ if
--   $$
--   \|x_i\|_0 \le k \qquad \text{for every } i = 1,\dots,n .
--   $$
--   The accuracy requirement (Definition 1) and the cost (3) quantify over exactly these profiles.
--
--   **Formalization Note** A binary vector is represented by its support $x_i \subseteq \{1,\dots,d\}$ (`Finset (Fin d)`), a bijection under which $\|x_i\|_0$ is the cardinality of the support.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section I, p.2, the range of the infimum in (2) and the supremum in (3)

import Mathlib

namespace SparseHistComm

/-- An input profile `x = (x₁, …, xₙ)` is **admissible** if every user's input is `k`-sparse:
`‖xᵢ‖₀ ≤ k` for all `i` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section I, p.2, the range of the infimum in (2) and of the supremum
in (3)).

**Formalization Note** A binary vector `xᵢ ∈ {0,1}^d` is represented by its support
`xᵢ : Finset (Fin d)`; this is a bijection, and `‖xᵢ‖₀ = (xᵢ).card`. -/
def Admissible {n d : ℕ} (k : ℕ) (x : Fin n → Finset (Fin d)) : Prop :=
  ∀ i, (x i).card ≤ k

end SparseHistComm


